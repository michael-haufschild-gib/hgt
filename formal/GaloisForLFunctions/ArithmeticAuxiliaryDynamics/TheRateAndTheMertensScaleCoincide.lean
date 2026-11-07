import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.AProducerBoundsTheMertensFunction

/-!
# The rate and the Mertens scale coincide

A producer of rate `ε` on `[1, K]` bounds `M(n)` by `3 ε n` past `K^{2+o(1)}`. A bound on `M` gives producers of comparable
rate on a polynomial alphabet. Neither direction uses a zero of `ζ`.

The harmonic sum `m(T) = Σ_{b ≤ T} μ(b)/b` is controlled by `M` alone. The identity `Σ_{d ≤ n} μ(d) ⌊n/d⌋ = 1` at `n = T V`, with
the hyperbola method above `T`, gives

`|m(T)| ≤ 2/V + η (2 + log V)`, when `|M(y)| ≤ η y` on `y ≥ T`.

So **the scale of the rate and the scale of the Mertens function are one scale**:

* at stretched exponentials: rates `exp(−(log K)^β)` for all `β < α` hold iff `|M(n)| ≤ n exp(−(log n)^β)` for all `β < α`;
* at powers: a polynomial rate exists iff `M(n) ≪ n^{1−σ}` for some `σ > 0`, and a rate `K^{-a}` gives every `σ < a/2`.

In particular, stencils beat Vinogradov–Korobov exactly when bounds on `M(x)` do. A certificate of a rate has no content beyond
a bound on `M(x)`; the only question it can pose is how to prove such a bound.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The hyperbola method above `T`: `Σ_{T < d ≤ TV} μ(d) ⌊TV/d⌋ = Σ_{r ≤ V} (M(TV/r) − M(T))`. -/
private lemma sum_moebius_floor_above {T V : ℕ} (hT : 1 ≤ T) (hV : 1 ≤ V) :
    ∑ d ∈ Ioc T (T * V), (ArithmeticFunction.moebius d : ℝ) * ((T * V / d : ℕ) : ℝ) =
      ∑ r ∈ Icc 1 V, (mertens (T * V / r) - mertens T) := by
  have hcount : ∀ d ∈ Ioc T (T * V), ((T * V / d : ℕ) : ℝ) =
      ∑ r ∈ Icc 1 V, if d ≤ T * V / r then (1 : ℝ) else 0 := by
    intro d hd
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hd
    have hd0 : 0 < d := by omega
    have hle : T * V / d ≤ V := Nat.div_le_of_le_mul (Nat.mul_le_mul_right V (by omega))
    have hfil : (Icc 1 V).filter (fun r => d ≤ T * V / r) = Icc 1 (T * V / d) := by
      ext r
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hr1, -⟩, hr2⟩
        refine ⟨hr1, (Nat.le_div_iff_mul_le hd0).mpr ?_⟩
        have := (Nat.le_div_iff_mul_le (by omega : 0 < r)).mp hr2
        rwa [mul_comm] at this
      · rintro ⟨hr1, hr2⟩
        refine ⟨⟨hr1, hr2.trans hle⟩, (Nat.le_div_iff_mul_le (by omega : 0 < r)).mpr ?_⟩
        have := (Nat.le_div_iff_mul_le hd0).mp hr2
        rwa [mul_comm] at this
    rw [← sum_filter, hfil]
    simp
  have hswap : ∑ d ∈ Ioc T (T * V), (ArithmeticFunction.moebius d : ℝ) * ((T * V / d : ℕ) : ℝ) =
      ∑ r ∈ Icc 1 V, ∑ d ∈ Ioc T (T * V),
        (ArithmeticFunction.moebius d : ℝ) * (if d ≤ T * V / r then (1 : ℝ) else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun d hd => ?_
    rw [hcount d hd, mul_sum]
  rw [hswap]
  refine sum_congr rfl fun r hr => ?_
  obtain ⟨hr1, hrV⟩ := mem_Icc.mp hr
  have hr0 : 0 < r := by omega
  have hTle : T ≤ T * V / r := (Nat.le_div_iff_mul_le hr0).mpr (Nat.mul_le_mul_left T hrV)
  have hle : T * V / r ≤ T * V := Nat.div_le_self _ _
  have hfil : (Ioc T (T * V)).filter (fun d => d ≤ T * V / r) = Ioc T (T * V / r) := by
    ext d
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3.trans hle⟩, h3⟩
  have hsum : ∑ d ∈ Ioc T (T * V), (ArithmeticFunction.moebius d : ℝ) *
      (if d ≤ T * V / r then (1 : ℝ) else 0) = ∑ d ∈ Ioc T (T * V / r), (ArithmeticFunction.moebius d : ℝ) := by
    rw [← hfil, sum_filter]
    refine sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [hsum, mertens, mertens, ← sum_Ioc_consecutive _ (Nat.zero_le T) hTle, add_sub_cancel_left]

/-- **The harmonic sum is controlled by the Mertens function.** If `|M(y)| ≤ η y` on `y ≥ T`, then for every `V ≥ 1`,
`|m(T)| ≤ 2/V + η (2 + log V)`. -/
theorem abs_mobiusHarmonic_le_of_mertens {T V : ℕ} (hT : 1 ≤ T) (hV : 1 ≤ V) {η : ℝ} (hη : 0 ≤ η)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y) :
    |mobiusHarmonic T| ≤ 2 / (V : ℝ) + η * (2 + Real.log V) := by
  obtain ⟨n, hn⟩ : ∃ n, n = T * V := ⟨_, rfl⟩
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hVR : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hT0 : (0 : ℝ) < T := by linarith
  have hV0 : (0 : ℝ) < V := by linarith
  have hnR : (n : ℝ) = T * V := by rw [hn]; push_cast; ring
  have hn0 : (0 : ℝ) < n := by rw [hnR]; positivity
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.mul_pos hT hV
  have hTn : T ≤ n := hn ▸ Nat.le_mul_of_pos_right T hV
  -- The identity at `n`.
  have hid : ∑ d ∈ Ioc 0 n, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) = 1 := by
    have hset : Ioc 0 n = Icc 1 n := by
      ext d
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [hset]
    exact RHTower.moebius_floor_summatory n hn1
  rw [← sum_Ioc_consecutive _ (Nat.zero_le T) hTn] at hid
  -- Above `T`.
  have habove : |∑ d ∈ Ioc T n, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)| ≤
      η * n * (2 + Real.log V) := by
    rw [hn, sum_moebius_floor_above hT hV, ← hn]
    have hterm : ∀ r ∈ Icc 1 V, |mertens (n / r) - mertens T| ≤ η * n * (1 / (r : ℝ)) + η * T := by
      intro r hr
      obtain ⟨hr1, hrV⟩ := mem_Icc.mp hr
      have hr0 : 0 < r := by omega
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
      have hTle : T ≤ n / r := by
        rw [hn]
        exact (Nat.le_div_iff_mul_le hr0).mpr (Nat.mul_le_mul_left T hrV)
      have h1 := hM _ hTle
      have h2 := hM T le_rfl
      have h3 : ((n / r : ℕ) : ℝ) ≤ (n : ℝ) / r := Nat.cast_div_le
      have h4 : η * ((n / r : ℕ) : ℝ) ≤ η * ((n : ℝ) / r) := mul_le_mul_of_nonneg_left h3 hη
      have h5 : η * ((n : ℝ) / r) = η * n * (1 / (r : ℝ)) := by ring
      calc |mertens (n / r) - mertens T| ≤ |mertens (n / r)| + |mertens T| := abs_sub _ _
        _ ≤ _ := by linarith
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    have hH : ∑ r ∈ Icc 1 V, 1 / (r : ℝ) ≤ 1 + Real.log V := by
      have h := harmonic_le_one_add_log V
      rw [harmonic_eq_sum_Icc] at h
      push_cast at h
      simpa [one_div] using h
    have hηn : 0 ≤ η * n := by positivity
    have h1 := mul_le_mul_of_nonneg_left hH hηn
    have h2 : (V : ℝ) * (η * T) = η * n := by
      rw [hnR]
      ring
    calc _ ≤ η * n * (1 + Real.log V) + η * n := by rw [h2]; linarith
      _ = _ := by ring
  -- Below `T`: replacing floors by real quotients costs at most `T`.
  have hbelow : |(n : ℝ) * mobiusHarmonic T -
      ∑ d ∈ Ioc 0 T, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)| ≤ T := by
    have hset : Icc 1 T = Ioc 0 T := by
      ext d
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [mobiusHarmonic, hset, mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Ioc 0 T, |(n : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / d) -
        (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)| ≤ 1 := by
      intro d hd
      have hd0 : 0 < d := (mem_Ioc.mp hd).1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
      have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := d)
        exact_mod_cast this
      have h1 : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
      have h2 : (n : ℝ) / d < ((n / d : ℕ) : ℝ) + 1 := by
        have h := Nat.lt_floor_add_one ((n : ℝ) / d)
        rwa [Nat.floor_div_eq_div] at h
      have heq : (n : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / d) -
          (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) =
          (ArithmeticFunction.moebius d : ℝ) * ((n : ℝ) / d - ((n / d : ℕ) : ℝ)) := by ring
      rw [heq, abs_mul]
      have h3 : |(n : ℝ) / d - ((n / d : ℕ) : ℝ)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      calc _ ≤ 1 * 1 := mul_le_mul hμ h3 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    refine (sum_le_sum hterm).trans ?_
    simp
  -- Assembly.
  have hnm : |(n : ℝ) * mobiusHarmonic T| ≤ T + 1 + η * n * (2 + Real.log V) := by
    have e : (n : ℝ) * mobiusHarmonic T =
        ((n : ℝ) * mobiusHarmonic T - ∑ d ∈ Ioc 0 T, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) +
          (1 - ∑ d ∈ Ioc T n, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) := by
      linarith
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h3 := abs_sub (1 : ℝ) (∑ d ∈ Ioc T n, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ))
    rw [abs_one] at h3
    linarith
  rw [abs_mul, abs_of_pos hn0] at hnm
  have hdiv : |mobiusHarmonic T| ≤ (T + 1 + η * n * (2 + Real.log V)) / n := by
    rw [le_div_iff₀ hn0, mul_comm]
    exact hnm
  refine hdiv.trans ?_
  have hsplit : ((T : ℝ) + 1 + η * n * (2 + Real.log V)) / n =
      1 / (V : ℝ) + 1 / ((T : ℝ) * V) + η * (2 + Real.log V) := by
    rw [hnR]
    field_simp
  rw [hsplit]
  have h1 : 1 / ((T : ℝ) * V) ≤ 1 / (V : ℝ) := by
    refine one_div_le_one_div_of_le hV0 ?_
    nlinarith
  have h2 : 2 / (V : ℝ) = 1 / (V : ℝ) + 1 / (V : ℝ) := by ring
  linarith

/-- With `V = ⌈1/η⌉`: `|m(T)| ≤ η (5 + log (1/η))`. -/
theorem abs_mobiusHarmonic_le_of_level {T : ℕ} (hT : 1 ≤ T) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hM : ∀ y, T ≤ y → |mertens y| ≤ η * y) :
    |mobiusHarmonic T| ≤ η * (5 + Real.log (1 / η)) := by
  obtain ⟨V, hV⟩ : ∃ V, V = ⌈1 / η⌉₊ := ⟨_, rfl⟩
  have hinv : 1 ≤ 1 / η := (one_le_div hη0).mpr hη1
  have hle : 1 / η ≤ V := hV ▸ Nat.le_ceil _
  have hlt : (V : ℝ) < 1 / η + 1 := hV ▸ Nat.ceil_lt_add_one (by linarith)
  have hVR : (1 : ℝ) ≤ V := by linarith
  have hV1 : 1 ≤ V := by exact_mod_cast hVR
  have hV0 : (0 : ℝ) < V := by linarith
  have h := abs_mobiusHarmonic_le_of_mertens hT hV1 hη0.le hM
  have h1 : 2 / (V : ℝ) ≤ 2 * η := by
    rw [div_le_iff₀ hV0]
    have : η * (1 / η) = 1 := by field_simp
    nlinarith
  have hlog : Real.log (V : ℝ) ≤ 1 + Real.log (1 / η) := by
    have h2 : (V : ℝ) ≤ 2 * (1 / η) := by linarith
    have h3 := Real.log_le_log hV0 h2
    rw [Real.log_mul (by norm_num) (by positivity)] at h3
    have h4 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have h5 : η * (2 + Real.log (V : ℝ)) ≤ η * (3 + Real.log (1 / η)) :=
    mul_le_mul_of_nonneg_left (by linarith) hη0.le
  have e : η * (5 + Real.log (1 / η)) = 2 * η + η * (3 + Real.log (1 / η)) := by ring
  rw [e]
  linarith

/-- **A stretched exponential bound on `M` is a Mertens level, at every smaller exponent.** -/
theorem isMertensLevel_of_mertens_exp {β β' : ℝ} (hβ0 : 0 < β) (hββ' : β < β') (hβ'1 : β' ≤ 1)
    (hM : ∀ᶠ n : ℕ in atTop, |mertens n| ≤ (n : ℝ) * Real.exp (-(Real.log (n : ℝ) ^ β'))) :
    IsMertensLevel fun T => Real.exp (-(Real.log (T : ℝ) ^ β)) := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hM
  have hβ'0 : 0 < β' := by linarith
  have hlog : Tendsto (fun T : ℕ => Real.log (T : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp1 := hlog.eventually (HTGeometry.eventually_mul_rpow_le_exp_rpow (18 : ℝ)
    (c := 1) (δ := β) (p := 1) one_pos hβ0)
  have hp2 := hlog.eventually ((tendsto_rpow_atTop (by linarith : 0 < β' - β)).eventually_ge_atTop 2)
  have hp3 := hlog.eventually ((tendsto_rpow_atTop hβ'0).eventually_ge_atTop 8)
  filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop 1, hlog.eventually_ge_atTop 1, hp1, hp2, hp3]
    with T hT1 hT2 hu1 h1 h2 h3
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (T : ℝ) := ⟨_, rfl⟩
  rw [← hu] at hu1 h1 h2 h3 ⊢
  have hu0 : 0 < u := by linarith
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT2
  have hT0 : (0 : ℝ) < T := by linarith
  rw [Real.rpow_one, one_mul] at h1
  have hsplit : u ^ β' = u ^ β * u ^ (β' - β) := by
    rw [← Real.rpow_add hu0]
    congr 1
    ring
  have hβp : 0 < u ^ β := Real.rpow_pos_of_pos hu0 _
  have hv : 2 * u ^ β ≤ u ^ β' := by
    rw [hsplit]
    nlinarith
  obtain ⟨η, hηdef⟩ : ∃ η, η = Real.exp (-(u ^ β')) := ⟨_, rfl⟩
  have hη0 : 0 < η := hηdef ▸ Real.exp_pos _
  have hη1 : η ≤ 1 := by
    rw [hηdef]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hηδ : η ≤ Real.exp (-(u ^ β)) := by
    rw [hηdef]
    exact Real.exp_le_exp.mpr (by linarith)
  have hMη : ∀ y, T ≤ y → |mertens y| ≤ η * y := by
    intro y hy
    have hyR : (T : ℝ) ≤ y := by exact_mod_cast hy
    have hlogy : u ≤ Real.log (y : ℝ) := hu ▸ Real.log_le_log hT0 hyR
    have hexp : Real.exp (-(Real.log (y : ℝ) ^ β')) ≤ η := by
      rw [hηdef]
      exact Real.exp_le_exp.mpr (neg_le_neg (Real.rpow_le_rpow hu0.le hlogy hβ'0.le))
    have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
    calc |mertens y| ≤ (y : ℝ) * Real.exp (-(Real.log (y : ℝ) ^ β')) := hN₁ y (hT1.trans hy)
      _ ≤ (y : ℝ) * η := mul_le_mul_of_nonneg_left hexp hy0
      _ = _ := mul_comm _ _
  refine ⟨Real.exp_pos _, ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr (by linarith)
  · -- `1/T = exp(−u) ≤ exp(−u^β)`, as `β ≤ 1 ≤ u`.
    have huβ : u ^ β ≤ u := by
      calc u ^ β ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
        _ = u := Real.rpow_one u
    have h4 : 1 / (T : ℝ) = Real.exp (-u) := by
      rw [hu, Real.exp_neg, Real.exp_log hT0, one_div]
    rw [h4]
    exact Real.exp_le_exp.mpr (by linarith)
  · intro y hy
    refine (hMη y hy).trans ?_
    exact mul_le_mul_of_nonneg_right hηδ (Nat.cast_nonneg y)
  · refine (abs_mobiusHarmonic_le_of_level hT2 hη0 hη1 hMη).trans ?_
    have hlogη : Real.log (1 / η) = u ^ β' := by
      rw [hηdef, one_div, Real.log_inv, Real.log_exp, neg_neg]
    rw [hlogη]
    -- `5 + v ≤ exp(v/2)` once `v ≥ 8`.
    obtain ⟨v, hvdef⟩ : ∃ v, v = u ^ β' := ⟨_, rfl⟩
    rw [← hvdef] at h3 hv ⊢
    have hexp := Real.quadratic_le_exp_of_nonneg (x := v / 2) (by linarith)
    have h5 : 5 + v ≤ Real.exp (v / 2) := by nlinarith
    calc η * (5 + v) ≤ Real.exp (-v) * Real.exp (v / 2) := by
          rw [hηdef, ← hvdef]
          exact mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
      _ = Real.exp (-(v / 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · -- `(3 + 6u) exp(−u^β) ≤ 1/2`.
    have hE := Real.exp_pos (u ^ β)
    rw [Real.exp_neg, inv_mul_le_iff₀ hE]
    nlinarith

/-- **The stretched exponential scales coincide.** For `0 < α ≤ 1`: rates `exp(−(log K)^β)` for all `β < α` hold if and only if
`|M(n)| ≤ n exp(−(log n)^β)` for all `β < α`. -/
theorem hasRate_exp_iff_mertens {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∀ β, 0 < β → β < α → HasRate fun K => Real.exp (-(Real.log (K : ℝ) ^ β))) ↔
      ∀ β, 0 < β → β < α → ∀ᶠ n : ℕ in atTop,
        |mertens n| ≤ (n : ℝ) * Real.exp (-(Real.log (n : ℝ) ^ β)) := by
  constructor
  · intro h β hβ0 hβ
    obtain ⟨β₁, hβ₁⟩ : ∃ β₁, β₁ = (β + α) / 2 := ⟨_, rfl⟩
    have h1 : β < β₁ := by rw [hβ₁]; linarith
    have h2 : β₁ < α := by rw [hβ₁]; linarith
    have hβ₁0 : 0 < β₁ := by linarith
    have hread := (h β₁ hβ₁0 h2).eventually_abs_mertens_le (θ := 1 / 3) (by norm_num) (by norm_num)
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (1 / 4 : ℝ) ^ β₁ := ⟨_, rfl⟩
    have hc : 0 < c := by rw [hcdef]; positivity
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hp1 := hlog.eventually ((tendsto_rpow_atTop (by linarith : 0 < β₁ - β)).eventually_ge_atTop (2 / c))
    have hp2 := hlog.eventually ((tendsto_rpow_atTop hβ0).eventually_ge_atTop (Real.log 3))
    have hcut : Tendsto (fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
    filter_upwards [hread, hp1, hp2, hlog.eventually_ge_atTop 12, hcut.eventually_ge_atTop 1,
      eventually_ge_atTop 1] with n hr h3 h4 h5 hK1 hn1
    obtain ⟨K, hKdef⟩ : ∃ K, K = ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ := ⟨_, rfl⟩
    rw [← hKdef] at hr hK1
    obtain ⟨u, hu⟩ : ∃ u, u = Real.log (n : ℝ) := ⟨_, rfl⟩
    rw [← hu] at h3 h4 h5 ⊢
    have hu0 : 0 < u := by linarith
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hKlt : (n : ℝ) ^ (1 / 3 : ℝ) < (K : ℝ) + 1 := hKdef ▸ Nat.lt_floor_add_one _
    -- `log K ≥ u/4`.
    have hKlow : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ K := by linarith
    have hlogK : u / 4 ≤ Real.log (K : ℝ) := by
      have h6 := Real.log_le_log (by positivity) hKlow
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hnR, ← hu] at h6
      have h7 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9
        linarith
      linarith
    have hpow : c * u ^ β₁ ≤ Real.log (K : ℝ) ^ β₁ := by
      have h6 := Real.rpow_le_rpow (by positivity) hlogK hβ₁0.le
      have e : (u / 4) ^ β₁ = c * u ^ β₁ := by
        rw [hcdef, div_eq_mul_inv, mul_comm, Real.mul_rpow (by norm_num) hu0.le]
        norm_num
      rwa [e] at h6
    have hsplit : u ^ β₁ = u ^ β * u ^ (β₁ - β) := by
      rw [← Real.rpow_add hu0]
      congr 1
      ring
    have hβp : 0 < u ^ β := Real.rpow_pos_of_pos hu0 _
    have h8 : 2 * u ^ β ≤ c * u ^ β₁ := by
      have h9 : 2 ≤ c * u ^ (β₁ - β) := by
        rwa [div_le_iff₀ hc, mul_comm] at h3
      rw [hsplit]
      nlinarith
    have hfinal : 3 * Real.exp (-(Real.log (K : ℝ) ^ β₁)) ≤ Real.exp (-(u ^ β)) := by
      have h3e : (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      calc 3 * Real.exp (-(Real.log (K : ℝ) ^ β₁))
          = Real.exp (Real.log 3 + -(Real.log (K : ℝ) ^ β₁)) := by
            rw [Real.exp_add, ← h3e]
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    have hn0 : (0 : ℝ) ≤ n := hnR.le
    calc |mertens n| ≤ 3 * Real.exp (-(Real.log (K : ℝ) ^ β₁)) * n := hr
      _ ≤ Real.exp (-(u ^ β)) * n := mul_le_mul_of_nonneg_right hfinal hn0
      _ = _ := mul_comm _ _
  · intro h β hβ0 hβ
    obtain ⟨β₁, hβ₁⟩ : ∃ β₁, β₁ = (β + α) / 2 := ⟨_, rfl⟩
    obtain ⟨β₂, hβ₂⟩ : ∃ β₂, β₂ = (β + β₁) / 2 := ⟨_, rfl⟩
    have h1 : β < β₁ := by rw [hβ₁]; linarith
    have h2 : β₁ < α := by rw [hβ₁]; linarith
    have h3 : β < β₂ := by rw [hβ₂]; linarith
    have h4 : β₂ < β₁ := by rw [hβ₂]; linarith
    exact hasRate_of_level_exp hβ0 h3
      (isMertensLevel_of_mertens_exp (by linarith) h4 (by linarith) (h β₁ (by linarith) h2))

/-- **A polynomial rate is a power bound on `M`.** A rate `K^{-a}` gives `|M(n)| ≤ C n^{1−σ}` for every `σ < a/2`, `σ ≤ 1`. -/
theorem HasRate.exists_abs_mertens_le_rpow {a σ : ℝ} (ha0 : 0 < a) (h : HasRate fun K => (K : ℝ) ^ (-a))
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hσ : σ < a / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |mertens n| ≤ C * (n : ℝ) ^ (1 - σ) := by
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = (σ / a + 1 / 2) / 2 := ⟨_, rfl⟩
  have hσa : σ / a < 1 / 2 := by
    rw [div_lt_iff₀ ha0]
    linarith
  have hσa0 : 0 < σ / a := by positivity
  have hθ0 : 0 < θ := by rw [hθdef]; linarith
  have hθ : θ < 1 / 2 := by rw [hθdef]; linarith
  have hθσ : σ ≤ a * θ := by
    have h1 : σ / a ≤ θ := by rw [hθdef]; linarith
    rw [div_le_iff₀ ha0] at h1
    linarith
  have hread := h.eventually_abs_mertens_le hθ0 hθ
  have hcut : Tendsto (fun n : ℕ => ⌊(n : ℝ) ^ θ⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop hθ0).comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hread.and (hcut.eventually_ge_atTop 1))
  refine ⟨3 * (2 : ℝ) ^ a + N₀, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow1 : 1 ≤ (n : ℝ) ^ (1 - σ) := Real.one_le_rpow hnR (by linarith)
  have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
  by_cases hnN : N₀ ≤ n
  · obtain ⟨hr, hK1⟩ := hN₀ n hnN
    obtain ⟨K, hKdef⟩ : ∃ K, K = ⌊(n : ℝ) ^ θ⌋₊ := ⟨_, rfl⟩
    rw [← hKdef] at hr hK1
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hKlt : (n : ℝ) ^ θ < (K : ℝ) + 1 := hKdef ▸ Nat.lt_floor_add_one _
    have hKlow : (n : ℝ) ^ θ / 2 ≤ K := by linarith
    have hKpow : (K : ℝ) ^ (-a) ≤ (2 : ℝ) ^ a * (n : ℝ) ^ (-(a * θ)) := by
      calc (K : ℝ) ^ (-a) ≤ ((n : ℝ) ^ θ / 2) ^ (-a) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hKlow (by linarith)
        _ = _ := by
            rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hn0.le,
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            have e : θ * -a = -(a * θ) := by ring
            rw [e]
            field_simp
    have hn1 : (n : ℝ) ^ (-(a * θ)) * n ≤ (n : ℝ) ^ (1 - σ) := by
      have e : (n : ℝ) ^ (-(a * θ)) * n = (n : ℝ) ^ (1 - a * θ) := by
        rw [sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one, mul_comm]
      rw [e]
      exact Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    have hnp : 0 ≤ (n : ℝ) ^ (1 - σ) := by linarith
    calc |mertens n| ≤ 3 * (K : ℝ) ^ (-a) * n := hr
      _ ≤ 3 * ((2 : ℝ) ^ a * (n : ℝ) ^ (-(a * θ))) * n := by gcongr
      _ = 3 * (2 : ℝ) ^ a * ((n : ℝ) ^ (-(a * θ)) * n) := by ring
      _ ≤ 3 * (2 : ℝ) ^ a * (n : ℝ) ^ (1 - σ) := by gcongr
      _ ≤ _ := by
          have : 0 ≤ (N₀ : ℝ) * (n : ℝ) ^ (1 - σ) := by positivity
          nlinarith
  · have hlt : (n : ℝ) ≤ N₀ := by exact_mod_cast (not_le.mp hnN).le
    have hM : |mertens n| ≤ n := by
      rw [mertens]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ b ∈ Ioc 0 n, |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
        intro b _
        have := ArithmeticFunction.abs_moebius_le_one (n := b)
        exact_mod_cast this
      refine (sum_le_sum hterm).trans ?_
      simp
    have h3 : 0 ≤ 3 * (2 : ℝ) ^ a * (n : ℝ) ^ (1 - σ) := by positivity
    have hNp : (N₀ : ℝ) ≤ N₀ * (n : ℝ) ^ (1 - σ) := le_mul_of_one_le_right hN0 hpow1
    nlinarith

/-- **The polynomial scales coincide.** A polynomial rate exists if and only if `M(n) ≪ n^{1−σ}` for some `σ > 0`. -/
theorem exists_hasRate_rpow_iff_mertens :
    (∃ a : ℝ, 0 < a ∧ HasRate fun K => (K : ℝ) ^ (-a)) ↔
      ∃ C σ : ℝ, 0 ≤ C ∧ 0 < σ ∧ ∀ n : ℕ, 1 ≤ n → |mertens n| ≤ C * (n : ℝ) ^ (1 - σ) := by
  constructor
  · rintro ⟨a, ha0, h⟩
    obtain ⟨σ, hσ⟩ : ∃ σ, σ = min (a / 4) 1 := ⟨_, rfl⟩
    have hσ0 : 0 < σ := by
      rw [hσ]
      exact lt_min (by linarith) one_pos
    have hσ1 : σ ≤ 1 := hσ ▸ min_le_right _ _
    have hσa : σ < a / 2 := lt_of_le_of_lt (hσ ▸ min_le_left _ _) (by linarith)
    obtain ⟨C, hC, hM⟩ := h.exists_abs_mertens_le_rpow ha0 hσ0 hσ1 hσa
    exact ⟨C, σ, hC, hσ0, hM⟩
  · rintro ⟨C, σ, hC, hσ0, hM⟩
    obtain ⟨τ, hτ⟩ : ∃ τ, τ = min σ 1 := ⟨_, rfl⟩
    have hτ0 : 0 < τ := by
      rw [hτ]
      exact lt_min hσ0 one_pos
    have hτ1 : τ ≤ 1 := hτ ▸ min_le_right _ _
    have hτσ : τ ≤ σ := hτ ▸ min_le_left _ _
    refine ⟨τ / 16, by positivity, hasRate_of_power hC hτ0 hτ1 fun n hn => ?_⟩
    rw [← mertens_eq_mertensM]
    refine (hM n hn).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
