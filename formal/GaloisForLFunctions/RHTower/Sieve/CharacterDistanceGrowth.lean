import GaloisForLFunctions.RHTower.Sieve.CharacterDistanceLower
import GaloisForLFunctions.RHTower.Sieve.ZetaLogPrimeSum
import GaloisForLFunctions.RHTower.ZetaVerticalLineBound
import GaloisForLFunctions.RHTower.Sieve.DistanceDiscTriangle
import GaloisForLFunctions.RHTower.Sieve.CharacterSeparation

/-!
# The distance between two characters grows with their separation

`CharacterDistanceLower.le_mulDistSqPair_charFn` reduces the character distance to an upper bound `L`
for the prime series at the difference frequency, and nothing in the folder supplies one.  At *small*
separation the supplier is the pole of `ζ`: at `N = 1` the Euler–Maclaurin carrier is `1 + 1/(s−1)`, so

`‖ζ(σ+iv)‖ ≤ 5 + 1/|v|`   for `1 ≤ σ ≤ 2`, `0 < |v| ≤ 2`,

and `|log‖ζ(s)‖ − ∑'_p Re(p^{−s})| ≤ π²/6` turns that into `∑'_p Re(p^{−σ−iv}) ≤ log(5 + 1/|v|) + π²/6`.
Against Mertens' second theorem this gives

`D(n^{it}, n^{iu}; z)² ≥ logLog z − log(5 + 1/|t−u|) − C`,

i.e. `≥ log(|t−u|·log z) − C'` up to the constants: the distance between two characters *grows* like the
logarithm of their separation measured in units of `1/log z`.

That is the mechanism behind Halász's factor `1 + m`.  The uniform supplier the folder already uses
(`sum_cos_div_prime_ge`, the zero-free region) loses `7 log log|t|` and so degrades with the height; this
one degrades with `1/|v|` instead, which is what makes the window on which `f` is close to a character
*narrow* rather than the distance small.  The narrow window is worth a factor `1/log z` of kernel mass,
which is exactly the `1/(σ−1)` that every pointwise route pays.
-/

noncomputable section
namespace RHTower.Sieve
open Complex RHTower

/-- **The pole bound for `ζ` at small frequency.**  Euler–Maclaurin at `N = 1`: the carrier is
`1 + 1/(s−1)` and the remainder is at most `‖s‖/σ ≤ 4`. -/
theorem norm_riemannZeta_le_inv_abs_im {s : ℂ} (hσ1 : 1 ≤ s.re) (hσ2 : s.re ≤ 2)
    (ht : |s.im| ≤ 2) (ht0 : s.im ≠ 0) :
    ‖riemannZeta s‖ ≤ 5 + 1 / |s.im| := by
  have hσ0 : (0 : ℝ) < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at ht0
    simp only [Complex.one_im] at ht0
    exact ht0 rfl
  have habs : (0 : ℝ) < |s.im| := abs_pos.2 ht0
  have hEM := zeta_sub_emCarrier_norm_le (N := 1) (le_refl 1) hσ0 hs1
  -- the Dirichlet polynomial part
  have hpoly : ‖dirichletPoly 1 s‖ ≤ 1 := by
    have h := norm_dirichletPoly_le_one_add_log (N := 1) (s := s) hσ1
    rw [Nat.cast_one, Real.log_one] at h
    linarith
  -- the pole part
  have hpole : ‖emPole 1 s‖ ≤ 1 / |s.im| := by
    rw [emPole, norm_div, Nat.cast_one, Complex.one_cpow, norm_one]
    have hden : |s.im| ≤ ‖s - 1‖ := by
      have h := Complex.abs_im_le_norm (s - 1)
      have him : (s - 1).im = s.im := by simp
      rwa [him] at h
    exact div_le_div_of_nonneg_left zero_le_one habs hden
  -- the remainder
  have hrem : ‖s‖ * (1 : ℝ) ^ (-s.re) / s.re ≤ 4 := by
    rw [Real.one_rpow, mul_one]
    have hnorm : ‖s‖ ≤ 4 := by
      have hre : |s.re| ≤ 2 := by
        rw [abs_of_nonneg hσ0.le]
        exact hσ2
      have h := Complex.norm_le_abs_re_add_abs_im s
      linarith
    calc ‖s‖ / s.re ≤ 4 / s.re := div_le_div_of_nonneg_right hnorm hσ0.le
      _ ≤ 4 / 1 := div_le_div_of_nonneg_left (by norm_num) zero_lt_one hσ1
      _ = 4 := by norm_num
  have hcar : ‖emCarrier 1 s‖ ≤ 1 + 1 / |s.im| := by
    rw [emCarrier]
    exact le_trans (norm_add_le _ _) (add_le_add hpoly hpole)
  have hsub : ‖riemannZeta s‖ ≤ ‖emCarrier 1 s‖ + ‖riemannZeta s - emCarrier 1 s‖ := by
    have := norm_add_le (emCarrier 1 s) (riemannZeta s - emCarrier 1 s)
    simpa using this
  have hcast : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [hcast] at hEM
  linarith [hEM, hcar, hsub, hrem]

/-- The prime series against `log‖ζ‖` from above, the mirror of `le_tsum_re_prime_cpow_of_log_le`. -/
theorem tsum_re_prime_cpow_le_of_log_le {σ t L : ℝ} (hσ : 1 < σ)
    (hL : Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ L) :
    (∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re)
      ≤ L + Real.pi ^ 2 / 6 := by
  have hre : (1 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have hcomp := abs_log_norm_riemannZeta_sub_tsum_re_le hre
  have habs := abs_le.1 hcomp
  have hsq : (∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2)
      = ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
    rw [tsum_norm_sq_eq]
    congr 1
    ext p
    congr 2
    simp
  have htail : (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ))) ≤ Real.pi ^ 2 / 6 :=
    tsum_prime_rpow_le hσ.le
  rw [hsq] at habs
  linarith [habs.1, habs.2]

/-- **The prime series at small frequency.**  The pole of `ζ` bounds it by `log(5 + 1/|t|)`. -/
theorem tsum_re_prime_cpow_le_small_freq {σ t : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (ht : |t| ≤ 2) (ht0 : t ≠ 0) :
    (∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re)
      ≤ Real.log (5 + 1 / |t|) + Real.pi ^ 2 / 6 := by
  have habs : (0 : ℝ) < |t| := abs_pos.2 ht0
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  have hzeta : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 5 + 1 / |t| := by
    have h := norm_riemannZeta_le_inv_abs_im (s := (σ : ℂ) + (t : ℂ) * Complex.I)
      (by rw [hre]; linarith) (by rw [hre]; exact hσ2) (by rw [him]; exact ht)
      (by rw [him]; exact ht0)
    rwa [him] at h
  have hpos : (0 : ℝ) < 5 + 1 / |t| := by positivity
  refine tsum_re_prime_cpow_le_of_log_le hσ1 ?_
  rcases le_or_gt ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ 0 with hle | hgt
  · have hzero : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ = 0 :=
      le_antisymm hle (norm_nonneg _)
    rw [hzero, Real.log_zero]
    exact Real.log_nonneg (by linarith [one_div_pos.2 habs])
  · exact Real.log_le_log hgt hzeta

/-- **The distance between two nearby characters grows with their separation.**  Mertens' second
theorem against the pole bound: the character distance is at least `logLog z − log(5 + 1/|t−u|)` up to
absolute constants. -/
theorem le_mulDistSqPair_charFn_small_freq {z : ℕ} (hz : 3 ≤ z) {t u : ℝ}
    (hd : |t - u| ≤ 2) (hd0 : t - u ≠ 0) :
    logLog z - mertensSecondLowerConst - (Real.log (5 + 1 / |t - u|) + Real.pi ^ 2 / 6)
        - 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
        - (1 + Real.log 4)
      ≤ mulDistSqPair (charFn t) (charFn u) (Nat.primesLE z) := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hexp : Real.exp 1 ≤ (z : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have hlogz1 : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have hlogz : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  have hσ1 : (1 : ℝ) < 1 + 1 / Real.log (z : ℝ) := by
    have : (0 : ℝ) < 1 / Real.log (z : ℝ) := by positivity
    linarith
  have hσ2 : 1 + 1 / Real.log (z : ℝ) ≤ 2 := by
    have : 1 / Real.log (z : ℝ) ≤ 1 := by
      rw [div_le_one hlogz]
      exact hlogz1
    linarith
  exact le_mulDistSqPair_charFn hz (tsum_re_prime_cpow_le_small_freq hσ1 hσ2 hd hd0)

/-- The explicit lower bound for the distance between two characters at separation `v`. -/
def charSepLower (z : ℕ) (v : ℝ) : ℝ :=
  logLog z - mertensSecondLowerConst - (Real.log (5 + 1 / |v|) + Real.pi ^ 2 / 6)
    - 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
    - (1 + Real.log 4)

theorem charSepLower_le_mulDistSqPair {z : ℕ} (hz : 3 ≤ z) {t u : ℝ}
    (hd : |t - u| ≤ 2) (hd0 : t - u ≠ 0) :
    charSepLower z (t - u) ≤ mulDistSqPair (charFn t) (charFn u) (Nat.primesLE z) :=
  le_mulDistSqPair_charFn_small_freq hz hd hd0

/-- **A function close to one character is far from every nearby character.**  The triangle inequality
for the multiplicative distance against the character separation bound: if `f` is within `√m` of
`charFn t₀`, then at separation `t − t₀` it is at least `√(charSepLower) − √m` from `charFn t`.

This is the mechanism behind Halász's factor `1 + m`: the window on which `f` can be close to *some*
character has width `≍ 1/log z`, because `charSepLower z v ≍ log(|v|·log z)` and the right side is
positive as soon as `|v| ≫ e^m/log z`. -/
theorem sqrt_charSepLower_sub_le_sqrt_mulDistSqPair {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {z : ℕ}
    (hz : 3 ≤ z) {t₀ t m : ℝ} (hd : |t - t₀| ≤ 2) (hd0 : t - t₀ ≠ 0)
    (hm : mulDistSqPair f (charFn t₀) (Nat.primesLE z) ≤ m) :
    Real.sqrt (charSepLower z (t - t₀)) - Real.sqrt m
      ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) := by
  have hP : ∀ p ∈ Nat.primesLE z, 0 < p := fun p hp => (Nat.prime_of_mem_primesLE hp).pos
  have hd' : |t₀ - t| ≤ 2 := by rwa [abs_sub_comm]
  have hd0' : t₀ - t ≠ 0 := fun h => hd0 (by linarith [sub_eq_zero.1 h])
  have hgrow := charSepLower_le_mulDistSqPair hz hd' hd0'
  have hsep : charSepLower z (t₀ - t) = charSepLower z (t - t₀) := by
    rw [charSepLower, charSepLower, abs_sub_comm]
  rw [hsep] at hgrow
  have htri := sqrt_mulDistSqPair_triangle_disc (f := charFn t₀) (g := f) (h := charFn t)
    (fun p _ => (norm_charFn t₀ p).le) (fun p _ => hf p) (fun p _ => (norm_charFn t p).le) hP
  have hcomm : mulDistSqPair (charFn t₀) f (Nat.primesLE z)
      = mulDistSqPair f (charFn t₀) (Nat.primesLE z) := mulDistSqPair_comm _ _ _
  rw [hcomm] at htri
  have hm' : Real.sqrt (mulDistSqPair f (charFn t₀) (Nat.primesLE z)) ≤ Real.sqrt m :=
    Real.sqrt_le_sqrt hm
  have hlow : Real.sqrt (charSepLower z (t - t₀))
      ≤ Real.sqrt (mulDistSqPair (charFn t₀) (charFn t) (Nat.primesLE z)) :=
    Real.sqrt_le_sqrt hgrow
  linarith [htri, hm', hlow]

/-- The squared form, valid once the separation bound dominates the closeness. -/
theorem le_mulDistSqPair_charFn_of_close {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {z : ℕ}
    (hz : 3 ≤ z) {t₀ t m : ℝ} (hd : |t - t₀| ≤ 2) (hd0 : t - t₀ ≠ 0)
    (hm : mulDistSqPair f (charFn t₀) (Nat.primesLE z) ≤ m)
    (hle : Real.sqrt m ≤ Real.sqrt (charSepLower z (t - t₀))) :
    (Real.sqrt (charSepLower z (t - t₀)) - Real.sqrt m) ^ 2
      ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  have hP : ∀ p ∈ Nat.primesLE z, 0 < p := fun p hp => (Nat.prime_of_mem_primesLE hp).pos
  have hnn : (0 : ℝ) ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) :=
    mulDistSqPair_nonneg_disc (fun p _ => hf p) (fun p _ => (norm_charFn t p).le) hP
  have hstep := sqrt_charSepLower_sub_le_sqrt_mulDistSqPair hf hz hd hd0 hm
  have hsq : Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ^ 2
      = mulDistSqPair f (charFn t) (Nat.primesLE z) := Real.sq_sqrt hnn
  rw [← hsq]
  exact pow_le_pow_left₀ (by linarith) hstep 2

/-- **Two characters cannot both be close to the same function.**  If `f` is within `√m` of both
`n^{it}` and `n^{iu}`, the triangle inequality forces `charSepLower z (t−u) ≤ 4m`.

This is the *global* form of the close-frequency dichotomy.  `HalaszDichotomy.eq_of_both_close` needs a
spacing hypothesis `|(t−u)·log p| ≤ π`, which confines it to a single multiplicative cell; here the only
hypothesis is `|t−u| ≤ 2`, because the separation bound comes from the pole of `ζ` rather than from a
cell-by-cell comparison. -/
theorem charSepLower_le_four_mul_of_both_close {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {z : ℕ}
    (hz : 3 ≤ z) {t u m : ℝ} (hd : |t - u| ≤ 2) (hd0 : t - u ≠ 0)
    (ht : mulDistSqPair f (charFn t) (Nat.primesLE z) ≤ m)
    (hu : mulDistSqPair f (charFn u) (Nat.primesLE z) ≤ m) :
    charSepLower z (t - u) ≤ 4 * m := by
  have hP : ∀ p ∈ Nat.primesLE z, 0 < p := fun p hp => (Nat.prime_of_mem_primesLE hp).pos
  have hm0 : (0 : ℝ) ≤ m :=
    le_trans (mulDistSqPair_nonneg_disc (fun p _ => hf p)
      (fun p _ => (norm_charFn t p).le) hP) ht
  rcases le_or_gt (charSepLower z (t - u)) 0 with hneg | hpos
  · linarith
  · have hgrow := charSepLower_le_mulDistSqPair hz hd hd0
    have htri := sqrt_mulDistSqPair_triangle_disc (f := charFn t) (g := f) (h := charFn u)
      (fun p _ => (norm_charFn t p).le) (fun p _ => hf p)
      (fun p _ => (norm_charFn u p).le) hP
    have hcomm : mulDistSqPair (charFn t) f (Nat.primesLE z)
        = mulDistSqPair f (charFn t) (Nat.primesLE z) := mulDistSqPair_comm _ _ _
    rw [hcomm] at htri
    have h1 : Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ Real.sqrt m :=
      Real.sqrt_le_sqrt ht
    have h2 : Real.sqrt (mulDistSqPair f (charFn u) (Nat.primesLE z)) ≤ Real.sqrt m :=
      Real.sqrt_le_sqrt hu
    have hlow : Real.sqrt (charSepLower z (t - u))
        ≤ Real.sqrt (mulDistSqPair (charFn t) (charFn u) (Nat.primesLE z)) :=
      Real.sqrt_le_sqrt hgrow
    have hsum : Real.sqrt (charSepLower z (t - u)) ≤ 2 * Real.sqrt m := by
      linarith [htri, hlow, h1, h2]
    have hsq : Real.sqrt (charSepLower z (t - u)) ^ 2 = charSepLower z (t - u) :=
      Real.sq_sqrt hpos.le
    have hms : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0
    nlinarith [hsum, hsq, hms, Real.sqrt_nonneg (charSepLower z (t - u)), Real.sqrt_nonneg m]

/-- **Close frequencies are confined to a window of width `≍ e^{4m}/log z`.**  The additive form of the
global dichotomy: unwinding `charSepLower`, two frequencies both within `√m` of `f` satisfy

`logLog z − C − 4m ≤ log(5 + 1/|t−u|)`,

so `|t−u|` cannot exceed a constant multiple of `e^{4m}/log z`. -/
theorem log_le_of_both_close {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {z : ℕ}
    (hz : 3 ≤ z) {t u m : ℝ} (hd : |t - u| ≤ 2) (hd0 : t - u ≠ 0)
    (ht : mulDistSqPair f (charFn t) (Nat.primesLE z) ≤ m)
    (hu : mulDistSqPair f (charFn u) (Nat.primesLE z) ≤ m) :
    logLog z - mertensSecondLowerConst - Real.pi ^ 2 / 6
        - 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
        - (1 + Real.log 4) - 4 * m
      ≤ Real.log (5 + 1 / |t - u|) := by
  have h := charSepLower_le_four_mul_of_both_close hf hz hd hd0 ht hu
  rw [charSepLower] at h
  linarith

end RHTower.Sieve
end
