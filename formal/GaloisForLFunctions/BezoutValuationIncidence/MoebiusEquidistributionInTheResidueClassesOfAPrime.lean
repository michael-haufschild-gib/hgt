import GaloisForLFunctions.BezoutValuationIncidence.OmittedResidueClassLawOfThePrimeRow
import GaloisForLFunctions.PNTPlus.Consequences
import GaloisForLFunctions.RHTower.Sieve.MoebiusMaximalWindow
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedDiscrepancyEnergyGrowthLaw

/-!
# The Möbius function in the residue classes of a prime

Fix a prime `p` and a class `0 < a < p`. The identity `μ log = -μ ⋆ Λ` and the hyperbola swap give

`Σ_{n ≤ x, n ≡ a} μ(n) log n = -Σ_{d ≤ x, p ∤ d} μ(d) Σ_{m ≤ x/d, m ≡ a d̄} Λ(m)`,

because `d m ≡ a (mod p)` forces `p ∤ d` and then `m ≡ a d̄`. By Dirichlet's theorem in Chebyshev form
each inner sum is `⌊x/d⌋/(p-1) + O(ε x/d + K_ε)`, uniformly over the `p - 1` coprime classes. The main
terms recombine into `Σ_{d ≤ x, p ∤ d} μ(d) ⌊x/d⌋ = O(x)` (the coprime Möbius harmonic sum is bounded
by `p/(p-1)`), and the errors sum to `O(ε x log x + K_ε x)`. Hence

`Σ_{n ≤ x, n ≡ a} μ(n) log n = o(x log x)`   (`eventually_abs_sum_class_moebius_log_le`).

This is the cancellation of the Möbius signs inside a single residue class of a single modulus, from
the nonvanishing of the Dirichlet `L`-functions modulo `p` on `Re s = 1` (through `WeakPNT_AP`). It is
qualitative: no rate, and no uniformity in `p`.
-/

open Finset Filter Topology
open ArithmeticFunction GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The twisted hyperbola swap -/

/-- **Twisted summatory swap.** `Σ_{n ≤ N} w(n) (f ⋆ g)(n) = Σ_{d ≤ N} f(d) Σ_{m ≤ N/d} w(dm) g(m)`. -/
theorem sum_Icc_mul_dirichletConv_twist (w : ℕ → ℝ) (f g : ArithmeticFunction ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, w n * (f * g) n = ∑ d ∈ Icc 1 N, f d * ∑ m ∈ Icc 1 (N / d), w (d * m) * g m := by
  have hexpand : ∑ n ∈ Icc 1 N, w n * (f * g) n =
      ∑ x ∈ (Icc 1 N).sigma (fun n => n.divisorsAntidiagonal), w x.1 * (f x.2.1 * g x.2.2) := by
    rw [sum_sigma]
    refine sum_congr rfl fun n _ => ?_
    rw [ArithmeticFunction.mul_apply, mul_sum]
  have hcollapse : ∑ d ∈ Icc 1 N, f d * ∑ m ∈ Icc 1 (N / d), w (d * m) * g m =
      ∑ x ∈ (Icc 1 N).sigma (fun d => Icc 1 (N / d)), w (x.1 * x.2) * (f x.1 * g x.2) := by
    rw [sum_sigma]
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  rw [hexpand, hcollapse]
  refine sum_nbij' (i := fun x => ⟨x.2.1, x.2.2⟩) (j := fun y => ⟨y.1 * y.2, (y.1, y.2)⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d, m⟩ hx
    rw [mem_sigma] at hx
    obtain ⟨hn, hdm⟩ := hx
    rw [mem_Icc] at hn
    rw [Nat.mem_divisorsAntidiagonal] at hdm
    obtain ⟨hprod, hn0⟩ := hdm
    dsimp only at hprod hn0 hn ⊢
    rw [mem_sigma, mem_Icc, mem_Icc]
    dsimp only
    have hd0 : d ≠ 0 := by intro h; rw [h, zero_mul] at hprod; omega
    have hm0 : m ≠ 0 := by intro h; rw [h, mul_zero] at hprod; omega
    refine ⟨⟨by omega, ?_⟩, by omega, ?_⟩
    · calc d ≤ d * m := Nat.le_mul_of_pos_right d (by omega)
        _ = n := hprod
        _ ≤ N := hn.2
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
      calc m * d = n := by rw [mul_comm]; exact hprod
        _ ≤ N := hn.2
  · rintro ⟨d, m⟩ hy
    rw [mem_sigma, mem_Icc, mem_Icc] at hy
    obtain ⟨hd, hm⟩ := hy
    dsimp only at hd hm ⊢
    rw [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal]
    have hdm : d * m ≤ N := le_trans (Nat.mul_le_mul_left d hm.2) (Nat.mul_div_le N d)
    have hne : d * m ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hne, hdm⟩, rfl, hne⟩
  · rintro ⟨n, d, m⟩ hx
    rw [mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    simp only [hx.2.1]
  · rintro ⟨d, m⟩ _
    rfl
  · rintro ⟨n, d, m⟩ hx
    rw [mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    simp only [hx.2.1]

/-- **The twisted `μ log` identity.**
`Σ_{n ≤ N} w(n) μ(n) log n = -Σ_{d ≤ N} μ(d) Σ_{m ≤ N/d} w(dm) Λ(m)`. -/
theorem sum_Icc_twist_moebius_log (w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, w n * (moebiusReal n * Real.log n) =
      -∑ d ∈ Icc 1 N, moebiusReal d * ∑ m ∈ Icc 1 (N / d), w (d * m) * vonMangoldt m := by
  have h := sum_Icc_mul_dirichletConv_twist w (↑moebius : ArithmeticFunction ℝ) (-vonMangoldt) N
  rw [← mu_log_eq_mu_mul_neg_lambda] at h
  have hl : ∀ n, mu_log n = moebiusReal n * Real.log n := fun n => by
    rw [mu_log_apply, ArithmeticFunction.log_apply]; rfl
  simp only [hl, ArithmeticFunction.intCoe_apply, ArithmeticFunction.neg_apply, mul_neg,
    sum_neg_distrib] at h
  rw [h]
  rfl

/-! ## §2. Reduction of the twisted class -/

/-- For `p ∤ d`, the condition `d m ≡ a` is one coprime class `m ≡ r` with `0 < r < p`. -/
theorem exists_class_of_not_dvd {p a d : ℕ} (hp : p.Prime) (ha0 : 0 < a) (hap : a < p)
    (hd : ¬ p ∣ d) : ∃ r, 0 < r ∧ r < p ∧ ∀ m, (d * m) % p = a ↔ m % p = r := by
  haveI := Fact.mk hp
  have ha : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt ha0 hap
  have hd' : (d : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hd
  set u : ZMod p := (a : ZMod p) * (d : ZMod p)⁻¹ with hudef
  have hu : u ≠ 0 := mul_ne_zero ha (inv_ne_zero hd')
  refine ⟨u.val, Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero]), ZMod.val_lt u, fun m => ?_⟩
  have hamod : a % p = a := Nat.mod_eq_of_lt hap
  have hrmod : u.val % p = u.val := Nat.mod_eq_of_lt (ZMod.val_lt u)
  rw [← hamod, ← ZMod.natCast_eq_natCast_iff', ← hrmod, ← ZMod.natCast_eq_natCast_iff',
    ZMod.natCast_zmod_val, Nat.cast_mul, hudef]
  constructor
  · intro h; rw [← h]; field_simp
  · intro h; rw [h]; field_simp

theorem mod_ne_of_dvd {p a d : ℕ} (ha0 : 0 < a) (hd : p ∣ d) (m : ℕ) : (d * m) % p ≠ a := by
  rw [Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hd m)]; omega

/-! ## §3. Uniform Chebyshev bounds over the coprime classes -/

/-- **Dirichlet in every coprime class, uniformly.** For `ε > 0` there is `K` with
`|Σ_{m ≤ y} (1_{m ≡ r} Λ(m) - 1/(p-1))| ≤ ε y + K` for all `y` and all `0 < r < p`. -/
theorem exists_abs_sum_classDefect_le_uniform {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r, 0 < r → r < p → ∀ y : ℕ,
      |∑ m ∈ Icc 1 y, classDefect p r m| ≤ ε * y + K := by
  have hall : ∀ᶠ y : ℕ in atTop, ∀ r ∈ (range p).filter (fun r => 0 < r),
      |∑ m ∈ Icc 1 y, classDefect p r m| ≤ ε * y := by
    rw [Filter.eventually_all_finset]
    intro r hr
    simp only [mem_filter, mem_range] at hr
    exact eventually_abs_sum_classDefect_le hp hr.2 hr.1 hε
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.mp hall
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hcd : ∀ r m, |classDefect p r m| ≤ Real.log m + 1 := by
    intro r m
    unfold classDefect
    have hinv : 0 ≤ 1 / ((p : ℝ) - 1) ∧ 1 / ((p : ℝ) - 1) ≤ 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by linarith)]
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    have hΛ : 0 ≤ (if m % p = r then vonMangoldt m else 0) ∧
        (if m % p = r then vonMangoldt m else 0) ≤ Real.log m := by
      split_ifs
      · exact ⟨vonMangoldt_nonneg, vonMangoldt_le_log⟩
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp
        · exact ⟨le_rfl, Real.log_nonneg (by exact_mod_cast hm)⟩
    rw [abs_le]; constructor <;> linarith [hΛ.1, hΛ.2, hinv.1, hinv.2]
  refine ⟨y₀ * (Real.log y₀ + 1), by
    have : 0 ≤ Real.log (y₀ : ℝ) := Real.log_natCast_nonneg y₀
    positivity, fun r hr0 hrp y => ?_⟩
  have hK0 : 0 ≤ (y₀ : ℝ) * (Real.log y₀ + 1) := by
    have : 0 ≤ Real.log (y₀ : ℝ) := Real.log_natCast_nonneg y₀
    positivity
  rcases le_or_gt y₀ y with hy | hy
  · have := hy₀ y hy r (by simp [hr0, hrp])
    linarith
  · have hsmall : |∑ m ∈ Icc 1 y, classDefect p r m| ≤ (y₀ : ℝ) * (Real.log y₀ + 1) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ m ∈ Icc 1 y, |classDefect p r m| ≤ ∑ _m ∈ Icc 1 y, (Real.log y₀ + 1) := by
            refine sum_le_sum fun m hm => (hcd r m).trans ?_
            rw [mem_Icc] at hm
            have : Real.log m ≤ Real.log y₀ :=
              Real.log_le_log (by exact_mod_cast (by omega : 0 < m))
                (by exact_mod_cast (by omega : m ≤ y₀))
            linarith
        _ = (y : ℝ) * (Real.log y₀ + 1) := by rw [sum_const, Nat.card_Icc]; simp; ring
        _ ≤ (y₀ : ℝ) * (Real.log y₀ + 1) := by
            refine mul_le_mul_of_nonneg_right (by exact_mod_cast hy.le) ?_
            have : 0 ≤ Real.log (y₀ : ℝ) := Real.log_natCast_nonneg y₀
            linarith
    have : 0 ≤ ε * y := by positivity
    linarith

/-! ## §4. The log-weighted class sum -/

theorem sum_Icc_inv_le_one_add_log (x : ℕ) : ∑ d ∈ Icc 1 x, 1 / (d : ℝ) ≤ 1 + Real.log x := by
  have h := harmonic_le_one_add_log x
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- The coprime main terms recombine: `|Σ_{d ≤ x, p ∤ d} μ(d) ⌊x/d⌋| ≤ 3x`. -/
theorem abs_sum_coprime_moebius_floor_le {p : ℕ} (hp : p.Prime) (x : ℕ) :
    |∑ d ∈ Icc 1 x, (if p ∣ d then 0 else moebiusReal d * ((x / d : ℕ) : ℝ))| ≤ 3 * x := by
  have hharm := abs_coprimeHarmonicMoebius_le_ratio hp.squarefree x
  have hratio : (p : ℝ) / (Nat.totient p : ℝ) ≤ 2 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one, div_le_iff₀ (by
      have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      linarith)]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hcop : ∀ d, Nat.Coprime d p ↔ ¬ p ∣ d := fun d => by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  have hsplit : ∑ d ∈ Icc 1 x, (if p ∣ d then 0 else moebiusReal d * ((x / d : ℕ) : ℝ)) =
      (x : ℝ) * coprimeHarmonicMoebius p x -
        ∑ d ∈ Icc 1 x, (if p ∣ d then 0 else moebiusReal d * ((x : ℝ) / d - ((x / d : ℕ) : ℝ))) := by
    rw [coprimeHarmonicMoebius, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    by_cases h : p ∣ d
    · simp [h, (hcop d).not_left.mpr h]
    · simp only [if_neg h]
      split_ifs with hc
      · ring
      · exact absurd ((hcop d).mpr h) hc
  have hfrac : ∀ d ∈ Icc 1 x,
      |if p ∣ d then 0 else moebiusReal d * ((x : ℝ) / d - ((x / d : ℕ) : ℝ))| ≤ 1 := by
    intro d hd
    rw [mem_Icc] at hd
    split_ifs
    · simp
    · have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have h1 : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / d := Nat.cast_div_le
      have h2 : (x : ℝ) / d - 1 < ((x / d : ℕ) : ℝ) := by
        have h := Nat.lt_div_mul_add (a := x) (show 0 < d by omega)
        have h' : (x : ℝ) < ((x / d : ℕ) : ℝ) * d + d := by exact_mod_cast h
        rw [div_sub_one hd0.ne', div_lt_iff₀ hd0]; linarith
      rw [abs_mul]
      have hμ : |moebiusReal d| ≤ 1 := abs_moebiusReal_le_one' d
      have hf : |(x : ℝ) / d - ((x / d : ℕ) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc |moebiusReal d| * |(x : ℝ) / d - ((x / d : ℕ) : ℝ)| ≤ 1 * 1 :=
            mul_le_mul hμ hf (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  rw [hsplit]
  calc _ ≤ |(x : ℝ) * coprimeHarmonicMoebius p x| +
        |∑ d ∈ Icc 1 x, (if p ∣ d then 0 else moebiusReal d * ((x : ℝ) / d - ((x / d : ℕ) : ℝ)))| :=
        abs_sub _ _
    _ ≤ (x : ℝ) * 2 + ∑ _d ∈ Icc 1 x, (1 : ℝ) := by
        rw [abs_mul, Nat.abs_cast]
        exact add_le_add (mul_le_mul_of_nonneg_left (hharm.trans hratio) (Nat.cast_nonneg x))
          ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hfrac))
    _ = 3 * x := by rw [sum_const, Nat.card_Icc]; simp; ring

/-- **Möbius cancellation inside one coprime class, with the logarithmic weight.** For a prime `p`,
`0 < a < p` and every `δ > 0`, eventually `|Σ_{n ≤ x, n ≡ a} μ(n) log n| ≤ δ x log x`. -/
theorem eventually_abs_sum_class_moebius_log_le {p a : ℕ} (hp : p.Prime) (ha0 : 0 < a)
    (hap : a < p) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, |∑ n ∈ Icc 1 x, (if n % p = a then 1 else 0) * (moebiusReal n * Real.log n)| ≤
      δ * x * Real.log x := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_sum_classDefect_le_uniform hp (show (0 : ℝ) < δ / 2 by positivity)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (2 * (3 + δ / 2 + K) / δ + 1),
    eventually_ge_atTop 1] with x hx hx1
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
  -- the inner sums: zero for `p ∣ d`, a coprime class otherwise
  have hinner : ∀ d ∈ Icc 1 x, ∃ D : ℝ, |D| ≤ δ / 2 * ((x / d : ℕ) : ℝ) + K ∧
      moebiusReal d * ∑ m ∈ Icc 1 (x / d), (if (d * m) % p = a then 1 else 0) * vonMangoldt m =
        (if p ∣ d then 0 else moebiusReal d * ((x / d : ℕ) : ℝ)) / ((p : ℝ) - 1) +
          (if p ∣ d then 0 else moebiusReal d * D) := by
    intro d _
    by_cases hd : p ∣ d
    · refine ⟨0, by simp; positivity, ?_⟩
      simp only [hd, if_true, zero_div, add_zero]
      rw [sum_eq_zero fun m _ => by rw [if_neg (mod_ne_of_dvd ha0 hd m), zero_mul], mul_zero]
    · obtain ⟨r, hr0, hrp, hr⟩ := exists_class_of_not_dvd hp ha0 hap hd
      refine ⟨∑ m ∈ Icc 1 (x / d), classDefect p r m, hK r hr0 hrp _, ?_⟩
      simp only [hd, if_false]
      have heq : ∑ m ∈ Icc 1 (x / d), (if (d * m) % p = a then 1 else 0) * vonMangoldt m =
          ∑ m ∈ Icc 1 (x / d), classDefect p r m + ((x / d : ℕ) : ℝ) / ((p : ℝ) - 1) := by
        simp only [classDefect, sum_sub_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul, hr]
        rw [Nat.add_sub_cancel]
        have : ∀ m, (if m % p = r then (1 : ℝ) else 0) * vonMangoldt m =
            if m % p = r then vonMangoldt m else 0 := fun m => by split_ifs <;> simp
        simp only [this]
        field_simp
        ring
      rw [heq]
      field_simp
      ring
  choose! D hD hDeq using hinner
  rw [sum_Icc_twist_moebius_log]
  simp only [mul_comm (if _ = a then (1 : ℝ) else 0)]
  have hrew : ∑ d ∈ Icc 1 x, moebiusReal d * ∑ m ∈ Icc 1 (x / d),
      (if (d * m) % p = a then 1 else 0) * vonMangoldt m =
      (∑ d ∈ Icc 1 x, (if p ∣ d then 0 else moebiusReal d * ((x / d : ℕ) : ℝ))) / ((p : ℝ) - 1) +
        ∑ d ∈ Icc 1 x, (if p ∣ d then 0 else moebiusReal d * D d) := by
    rw [sum_div, ← sum_add_distrib]
    exact sum_congr rfl fun d hd => hDeq d hd
  have hrew' : ∑ d ∈ Icc 1 x, moebiusReal d * ∑ m ∈ Icc 1 (x / d),
      vonMangoldt m * (if (d * m) % p = a then 1 else 0) =
      ∑ d ∈ Icc 1 x, moebiusReal d * ∑ m ∈ Icc 1 (x / d),
        (if (d * m) % p = a then 1 else 0) * vonMangoldt m := by
    refine sum_congr rfl fun d _ => ?_
    congr 1
    exact sum_congr rfl fun m _ => mul_comm _ _
  rw [abs_neg, hrew', hrew]
  have hmain := abs_sum_coprime_moebius_floor_le hp x
  have herr : |∑ d ∈ Icc 1 x, (if p ∣ d then 0 else moebiusReal d * D d)| ≤
      δ / 2 * x * (1 + Real.log x) + K * x := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ Icc 1 x, |if p ∣ d then 0 else moebiusReal d * D d|
        ≤ ∑ d ∈ Icc 1 x, (δ / 2 * ((x : ℝ) * (1 / d)) + K) := by
          refine sum_le_sum fun d hd => ?_
          rw [mem_Icc] at hd
          have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
          have hfl : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) * (1 / d) := by
            rw [mul_one_div]; exact Nat.cast_div_le
          split_ifs
          · simp only [abs_zero]; positivity
          · rw [abs_mul]
            calc |moebiusReal d| * |D d| ≤ 1 * (δ / 2 * ((x / d : ℕ) : ℝ) + K) :=
                  mul_le_mul (abs_moebiusReal_le_one' d) (hD d (mem_Icc.mpr hd)) (abs_nonneg _)
                    zero_le_one
              _ ≤ δ / 2 * ((x : ℝ) * (1 / d)) + K := by
                  rw [one_mul]; gcongr
      _ = δ / 2 * x * ∑ d ∈ Icc 1 x, 1 / (d : ℝ) + K * x := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, Nat.card_Icc]; simp; ring
      _ ≤ δ / 2 * x * (1 + Real.log x) + K * x := by
          gcongr; exact sum_Icc_inv_le_one_add_log x
  have hpinv : 1 / ((p : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hfirst : |(∑ d ∈ Icc 1 x, (if p ∣ d then 0 else moebiusReal d * ((x / d : ℕ) : ℝ))) /
      ((p : ℝ) - 1)| ≤ 3 * x := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (p : ℝ) - 1), div_eq_mul_one_div]
    calc _ ≤ 3 * (x : ℝ) * 1 := mul_le_mul hmain hpinv (by positivity) (by positivity)
      _ = 3 * x := mul_one _
  have hbig : (3 + δ / 2 + K) * x ≤ δ / 2 * x * Real.log x := by
    have h1 : 2 * (3 + δ / 2 + K) / δ ≤ Real.log x := by linarith
    have h2 : (3 + δ / 2 + K) ≤ δ / 2 * Real.log x := by
      rw [div_le_iff₀ hδ] at h1; linarith
    nlinarith
  calc _ ≤ |(∑ d ∈ Icc 1 x, (if p ∣ d then 0 else moebiusReal d * ((x / d : ℕ) : ℝ))) /
        ((p : ℝ) - 1)| + |∑ d ∈ Icc 1 x, (if p ∣ d then 0 else moebiusReal d * D d)| :=
        abs_add_le _ _
    _ ≤ 3 * x + (δ / 2 * x * (1 + Real.log x) + K * x) := add_le_add hfirst herr
    _ ≤ δ * x * Real.log x := by nlinarith

end

end GaloisForLFunctions.BezoutValuationIncidence
