import GaloisForLFunctions.RHTower.FloorTransformPowerThreshold
import GaloisForLFunctions.RHTower.SquarefreeLowerDensity

/-!
# The critical floor Wiener class

For an arithmetic weight `a` the truncated critical condition number is

`‖a‖_{1/2;N} = ∑_{d ≤ N} |a d| d^{-1/2}`,

and `a` is *critically subpower* when `‖a‖_{1/2;N} = N^{o(1)}`.  A profile has *critical type zero*
when it is `O_ε(N^{1/2+ε})` for every `ε > 0`.

A single Abel-free estimate shows that a critically subpower weight maps critical type zero to
critical type zero: splitting `ε` in half, the profile bound is applied with the smaller exponent
and the weight sum is majorized by the critical condition number.  If moreover `a` and `b` are
Dirichlet inverse and both critically subpower, floor associativity `T_b T_a = Id` runs the
estimate in both directions, so

`N^{-1/2} (T_a f)(N)` has type zero  ⟺  `N^{-1/2} f(N)` has type zero.

The class is exactly delimited by the power weights: `d^{-θ}` and `μ(d) d^{-θ}` are critically
subpower for `θ ≥ 1/2` (bounded above the threshold, logarithmic at it) and fail below it, where
the critical condition number already has the positive power `N^{1/2-θ}`.  In particular the
Tatuzawa–Iseki weight `a = 1` and its Möbius inverse both have critical condition number of exact
order `√N`, so the transform that they generate leaves the class.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The critical condition number -/

/-- **(24.34)** The truncated critical condition number `‖a‖_{1/2;N} = ∑_{d ≤ N} |a d| d^{-1/2}`. -/
def criticalNorm (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, |a d| * (d : ℝ) ^ (-(1 / 2 : ℝ))

theorem criticalNorm_nonneg (a : ℕ → ℝ) (N : ℕ) : 0 ≤ criticalNorm a N := by
  refine Finset.sum_nonneg fun d _ => ?_
  exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

theorem criticalNorm_le_of_abs_le {a b : ℕ → ℝ} (h : ∀ d : ℕ, 1 ≤ d → |a d| ≤ |b d|) (N : ℕ) :
    criticalNorm a N ≤ criticalNorm b N := by
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  exact mul_le_mul_of_nonneg_right (h d hd.1) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

/-- A weight is critically subpower when its truncated critical condition number is `N^{o(1)}`. -/
def CriticallySubpower (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → criticalNorm a N ≤ C * (N : ℝ) ^ ε

/-- A profile has critical type zero when it is `O_ε(N^{1/2+ε})` for every `ε > 0`. -/
def CriticalTypeZero (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → |f N| ≤ C * (N : ℝ) ^ (1 / 2 + ε)

theorem CriticallySubpower.mono {a b : ℕ → ℝ} (hb : CriticallySubpower b)
    (h : ∀ d : ℕ, 1 ≤ d → |a d| ≤ |b d|) : CriticallySubpower a := by
  intro ε hε
  obtain ⟨C, hC⟩ := hb ε hε
  exact ⟨C, fun N hN => le_trans (criticalNorm_le_of_abs_le h N) (hC N hN)⟩

theorem criticalTypeZero_congr {f g : ℕ → ℝ} (h : ∀ N : ℕ, 1 ≤ N → f N = g N)
    (hf : CriticalTypeZero f) : CriticalTypeZero g := by
  intro ε hε
  obtain ⟨C, hC⟩ := hf ε hε
  exact ⟨C, fun N hN => by rw [← h N hN]; exact hC N hN⟩

/-! ## The critical estimate -/

/-- **(24.35)** The critical condition number majorizes the floor transform of a critically
bounded profile. -/
theorem abs_floorTransform_le_criticalNorm {a f : ℕ → ℝ} {C delta : ℝ} (hC : 0 ≤ C)
    (hdelta : 0 ≤ delta)
    (hf : ∀ M : ℕ, 1 ≤ M → |f M| ≤ C * (M : ℝ) ^ (1 / 2 + delta)) {N : ℕ} (hN : 1 ≤ N) :
    |floorTransform a f N| ≤ C * (N : ℝ) ^ (1 / 2 + delta) * criticalNorm a N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [floorTransform]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [criticalNorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  obtain ⟨hd1, hdN⟩ := hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hquot : 1 ≤ N / d := (Nat.one_le_div_iff hd1).2 hdN
  have hfd := hf (N / d) hquot
  have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hrp : ((N / d : ℕ) : ℝ) ^ (1 / 2 + delta) ≤ ((N : ℝ) / (d : ℝ)) ^ (1 / 2 + delta) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcast (by linarith)
  have hsplit : ((N : ℝ) / (d : ℝ)) ^ (1 / 2 + delta)
      = (N : ℝ) ^ (1 / 2 + delta) * ((d : ℝ) ^ (1 / 2 + delta))⁻¹ := by
    rw [Real.div_rpow hNpos.le hdpos.le]
    ring
  have hpowle : ((d : ℝ) ^ (1 / 2 + delta))⁻¹ ≤ (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg hdpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hd1R (by linarith)
  have hnn : (0 : ℝ) ≤ C * (N : ℝ) ^ (1 / 2 + delta) :=
    mul_nonneg hC (Real.rpow_nonneg hNpos.le _)
  calc |a d * f (N / d)| = |a d| * |f (N / d)| := abs_mul _ _
    _ ≤ |a d| * (C * ((N / d : ℕ) : ℝ) ^ (1 / 2 + delta)) :=
        mul_le_mul_of_nonneg_left hfd (abs_nonneg _)
    _ ≤ |a d| * (C * ((N : ℝ) / (d : ℝ)) ^ (1 / 2 + delta)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp hC) (abs_nonneg _)
    _ = C * (N : ℝ) ^ (1 / 2 + delta) * (|a d| * ((d : ℝ) ^ (1 / 2 + delta))⁻¹) := by
        rw [hsplit]
        ring
    _ ≤ C * (N : ℝ) ^ (1 / 2 + delta) * (|a d| * (d : ℝ) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpowle (abs_nonneg _)) hnn

/-- **(24.35)** A critically subpower weight preserves critical type zero. -/
theorem criticalTypeZero_floorTransform {a f : ℕ → ℝ} (ha : CriticallySubpower a)
    (hf : CriticalTypeZero f) : CriticalTypeZero (floorTransform a f) := by
  intro ε hε
  obtain ⟨C₁, hC₁⟩ := hf (ε / 2) (by linarith)
  obtain ⟨C₂, hC₂⟩ := ha (ε / 2) (by linarith)
  have hone : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
  have hC₁0 : 0 ≤ C₁ := by
    have h := hC₁ 1 le_rfl
    rw [hone, Real.one_rpow, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hC₂0 : 0 ≤ C₂ := by
    have h := hC₂ 1 le_rfl
    rw [hone, Real.one_rpow, mul_one] at h
    exact le_trans (criticalNorm_nonneg a 1) h
  refine ⟨C₁ * C₂, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (1 / 2 + ε / 2) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ (1 / 2 + ε) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hbase := abs_floorTransform_le_criticalNorm (a := a) (f := f) hC₁0 (by linarith) hC₁ hN
  have hstep : C₁ * (N : ℝ) ^ (1 / 2 + ε / 2) * criticalNorm a N
      ≤ C₁ * (N : ℝ) ^ (1 / 2 + ε / 2) * (C₂ * (N : ℝ) ^ (ε / 2)) :=
    mul_le_mul_of_nonneg_left (hC₂ N hN)
      (mul_nonneg hC₁0 (Real.rpow_nonneg hNpos.le _))
  refine le_trans hbase (le_trans hstep (le_of_eq ?_))
  rw [← hpow]
  ring

/-! ## Exact inversion -/

/-- A Dirichlet-inverse pair of weights gives an exactly inverse pair of floor transforms. -/
theorem floorTransform_comp_of_unit {a b : ℕ → ℝ}
    (hab : ∀ n : ℕ, n ≠ 0 → dirichletConv a b n = unitWeight n) (f : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    floorTransform a (floorTransform b f) N = f N := by
  rw [floorTransform_comp]
  have hfun : floorTransform (dirichletConv a b) f N = floorTransform unitWeight f N := by
    rw [floorTransform, floorTransform]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    rw [hab d (by omega)]
  rw [hfun, floorTransform_unitWeight f hN]

/-- **(24.36) The critical floor Wiener lemma.**  A Dirichlet-invertible floor transform whose
weight and inverse weight are both critically subpower preserves critical type zero exactly. -/
theorem criticalTypeZero_floorTransform_iff {a b f : ℕ → ℝ} (ha : CriticallySubpower a)
    (hb : CriticallySubpower b) (hab : ∀ n : ℕ, n ≠ 0 → dirichletConv b a n = unitWeight n) :
    CriticalTypeZero (floorTransform a f) ↔ CriticalTypeZero f := by
  refine ⟨fun h => ?_, fun h => criticalTypeZero_floorTransform ha h⟩
  refine criticalTypeZero_congr (f := floorTransform b (floorTransform a f)) ?_
    (criticalTypeZero_floorTransform hb h)
  intro N hN
  exact floorTransform_comp_of_unit hab f hN

/-! ## The critical condition number of the power weights -/

theorem criticalNorm_powerWeight (theta : ℝ) (N : ℕ) :
    criticalNorm (powerWeight theta) N
      = ∑ d ∈ Finset.Icc 1 N, (d : ℝ) ^ (-(theta + 1 / 2)) := by
  rw [criticalNorm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
  rw [powerWeight, abs_of_nonneg (Real.rpow_nonneg hdpos.le _), ← Real.rpow_add hdpos]
  congr 1
  ring

theorem abs_moebiusPowerWeight_le_abs_powerWeight (theta : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    |moebiusPowerWeight theta d| ≤ |powerWeight theta d| := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [powerWeight, abs_of_nonneg (Real.rpow_nonneg hdpos.le _)]
  exact abs_moebiusPowerWeight_le hd

/-- Above the threshold the critical condition number is bounded. -/
theorem criticalNorm_powerWeight_le_tsum {theta : ℝ} (h : 1 / 2 < theta) (N : ℕ) :
    criticalNorm (powerWeight theta) N ≤ ∑' d : ℕ, (d : ℝ) ^ (-(theta + 1 / 2)) := by
  have hsum : Summable (fun d : ℕ => (d : ℝ) ^ (-(theta + 1 / 2))) := by
    have hstep : Summable (fun d : ℕ => ((d : ℝ) ^ (theta + 1 / 2))⁻¹) :=
      Real.summable_nat_rpow_inv.2 (by linarith)
    exact hstep.congr fun d => (Real.rpow_neg (Nat.cast_nonneg d) _).symm
  rw [criticalNorm_powerWeight]
  exact Summable.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _) hsum

/-- **Above the threshold the power weight is critically subpower.** -/
theorem criticallySubpower_powerWeight {theta : ℝ} (h : 1 / 2 < theta) :
    CriticallySubpower (powerWeight theta) := by
  intro ε hε
  refine ⟨∑' d : ℕ, (d : ℝ) ^ (-(theta + 1 / 2)), fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hrp : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hbound := criticalNorm_powerWeight_le_tsum h N
  have hnn : (0 : ℝ) ≤ ∑' d : ℕ, (d : ℝ) ^ (-(theta + 1 / 2)) :=
    le_trans (criticalNorm_nonneg _ 1) (criticalNorm_powerWeight_le_tsum h 1)
  nlinarith

/-! ## The logarithmic borderline -/

/-- The harmonic number is majorized by `1 + log n`. -/
theorem harmonicSum_le_one_add_log {n : ℕ} (hn : 1 ≤ n) :
    harmonicSum n ≤ 1 + Real.log n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [harmonicSum]
  | succ n hn ih =>
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hlog : (1 : ℝ) / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
      have hdiv : Real.log ((n : ℝ) / ((n : ℝ) + 1)) ≤ (n : ℝ) / ((n : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hn1)] at hdiv
      have hval : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
        field_simp
        ring
      rw [hval] at hdiv
      linarith
    rw [harmonicSum_succ]
    push_cast
    linarith

/-- At the threshold the critical condition number is the harmonic number. -/
theorem criticalNorm_powerWeight_half (N : ℕ) :
    criticalNorm (powerWeight (1 / 2)) N = harmonicSum N := by
  rw [criticalNorm_powerWeight, harmonicSum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
  rw [show -((1 : ℝ) / 2 + 1 / 2) = -(1 : ℝ) by norm_num, Real.rpow_neg hdpos.le, Real.rpow_one]
  exact (one_div _).symm

/-- A logarithmic critical condition number is already critically subpower. -/
theorem criticallySubpower_of_le_one_add_log {a : ℕ → ℝ}
    (h : ∀ N : ℕ, 1 ≤ N → criticalNorm a N ≤ 1 + Real.log N) : CriticallySubpower a := by
  intro ε hε
  refine ⟨1 + 1 / ε, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hrp : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hlog : ε * Real.log N ≤ (N : ℝ) ^ ε - 1 := by
    have hstep := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hNpos ε)
    rwa [Real.log_rpow hNpos] at hstep
  have hεinv : (0 : ℝ) < 1 / ε := by positivity
  have hgap : (1 + 1 / ε) * (N : ℝ) ^ ε - (1 + ((N : ℝ) ^ ε - 1) / ε)
      = (N : ℝ) ^ ε - 1 + 1 / ε := by
    field_simp
    ring
  have hdiv : Real.log N ≤ ((N : ℝ) ^ ε - 1) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hmain := h N hN
  linarith

/-- **At the threshold the power weight is critically subpower.** -/
theorem criticallySubpower_powerWeight_half : CriticallySubpower (powerWeight (1 / 2)) :=
  criticallySubpower_of_le_one_add_log fun N hN => by
    rw [criticalNorm_powerWeight_half]
    exact harmonicSum_le_one_add_log hN

/-- **The Möbius power weight is critically subpower at and above the threshold.** -/
theorem criticallySubpower_moebiusPowerWeight {theta : ℝ} (h : 1 / 2 ≤ theta) :
    CriticallySubpower (moebiusPowerWeight theta) := by
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [← heq]
    exact criticallySubpower_powerWeight_half.mono
      fun d hd => abs_moebiusPowerWeight_le_abs_powerWeight (1 / 2) hd
  · exact (criticallySubpower_powerWeight hlt).mono
      fun d hd => abs_moebiusPowerWeight_le_abs_powerWeight theta hd

/-! ## The Wiener class contains the whole stable power family -/

/-- **(24.36) applied to the power family.**  At and above the critical threshold the weighted
floor transform preserves critical type zero exactly. -/
theorem criticalTypeZero_floorTransform_powerWeight_iff {theta : ℝ} (h : 1 / 2 ≤ theta)
    (f : ℕ → ℝ) :
    CriticalTypeZero (floorTransform (powerWeight theta) f) ↔ CriticalTypeZero f := by
  have ha : CriticallySubpower (powerWeight theta) := by
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [← heq]
      exact criticallySubpower_powerWeight_half
    · exact criticallySubpower_powerWeight hlt
  exact criticalTypeZero_floorTransform_iff ha (criticallySubpower_moebiusPowerWeight h)
    (fun n hn => dirichletConv_moebiusPower_power theta hn)

/-! ## The threshold is sharp -/

/-- Below the threshold the critical condition number already carries a positive power. -/
theorem rpow_le_criticalNorm_powerWeight {theta : ℝ} (htheta : 0 ≤ theta) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 / 2 - theta) ≤ criticalNorm (powerWeight theta) N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [criticalNorm_powerWeight]
  have hterm : ∀ d ∈ Finset.Icc 1 N,
      (N : ℝ) ^ (-(theta + 1 / 2)) ≤ (d : ℝ) ^ (-(theta + 1 / 2)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
    have hdN : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hd.2
    exact Real.rpow_le_rpow_of_nonpos hdpos hdN (by linarith)
  have hconst : ∑ _d ∈ Finset.Icc 1 N, (N : ℝ) ^ (-(theta + 1 / 2))
      = (N : ℝ) * (N : ℝ) ^ (-(theta + 1 / 2)) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    congr 1
  have hexp : (N : ℝ) * (N : ℝ) ^ (-(theta + 1 / 2)) = (N : ℝ) ^ (1 / 2 - theta) := by
    nth_rewrite 1 [show (N : ℝ) = (N : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  calc (N : ℝ) ^ (1 / 2 - theta) = ∑ _d ∈ Finset.Icc 1 N, (N : ℝ) ^ (-(theta + 1 / 2)) := by
        rw [hconst, hexp]
    _ ≤ ∑ d ∈ Finset.Icc 1 N, (d : ℝ) ^ (-(theta + 1 / 2)) := Finset.sum_le_sum hterm

/-- A positive power lower bound on the critical condition number excludes the Wiener class. -/
theorem not_criticallySubpower_of_powerLower {a : ℕ → ℝ} {c c₀ : ℝ} (hc : 0 < c) (hc₀ : 0 < c₀)
    (h : ∀ N : ℕ, 1 ≤ N → c₀ * (N : ℝ) ^ c ≤ criticalNorm a N) : ¬ CriticallySubpower a := by
  intro hsub
  obtain ⟨C, hC⟩ := hsub (c / 2) (by linarith)
  have htend : Filter.Tendsto (fun K : ℕ => (K : ℝ) ^ (c / 2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hKgt, hK1⟩ :=
    ((htend.eventually_gt_atTop (C / c₀)).and (Filter.eventually_ge_atTop 1)).exists
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hsplit : (K : ℝ) ^ c = (K : ℝ) ^ (c / 2) * (K : ℝ) ^ (c / 2) := by
    rw [← Real.rpow_add hKpos]
    congr 1
    ring
  have hpos : (0 : ℝ) < (K : ℝ) ^ (c / 2) := Real.rpow_pos_of_pos hKpos _
  have hchain : c₀ * ((K : ℝ) ^ (c / 2) * (K : ℝ) ^ (c / 2)) ≤ C * (K : ℝ) ^ (c / 2) := by
    have h1 := h K hK1
    have h2 := hC K hK1
    rw [hsplit] at h1
    linarith
  have hcancel : c₀ * (K : ℝ) ^ (c / 2) ≤ C := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc c₀ * (K : ℝ) ^ (c / 2) * (K : ℝ) ^ (c / 2)
        = c₀ * ((K : ℝ) ^ (c / 2) * (K : ℝ) ^ (c / 2)) := by ring
      _ ≤ C * (K : ℝ) ^ (c / 2) := hchain
  rw [div_lt_iff₀ hc₀] at hKgt
  nlinarith

/-- **Below the threshold the power weight leaves the Wiener class.** -/
theorem not_criticallySubpower_powerWeight {theta : ℝ} (htheta : 0 ≤ theta)
    (hlt : theta < 1 / 2) : ¬ CriticallySubpower (powerWeight theta) := by
  refine not_criticallySubpower_of_powerLower (c := 1 / 2 - theta) (c₀ := 1)
    (by linarith) one_pos fun N hN => ?_
  rw [one_mul]
  exact rpow_le_criticalNorm_powerWeight htheta hN

/-! ## The Tatuzawa–Iseki weight and its Möbius inverse both leave the class -/

theorem powerWeight_zero (d : ℕ) : powerWeight 0 d = 1 := by
  rw [powerWeight, neg_zero, Real.rpow_zero]

theorem moebiusPowerWeight_zero (d : ℕ) :
    moebiusPowerWeight 0 d = (ArithmeticFunction.moebius d : ℝ) := by
  rw [moebiusPowerWeight, neg_zero, Real.rpow_zero, mul_one]

/-- **The constant weight has critical condition number at least `√N`.** -/
theorem sqrt_le_criticalNorm_powerWeight_zero {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt N ≤ criticalNorm (powerWeight 0) N := by
  have hbase := rpow_le_criticalNorm_powerWeight (theta := 0) le_rfl hN
  rw [Real.sqrt_eq_rpow]
  simpa using hbase

/-- **The Tatuzawa–Iseki weight is not critically subpower.** -/
theorem not_criticallySubpower_powerWeight_zero : ¬ CriticallySubpower (powerWeight 0) :=
  not_criticallySubpower_powerWeight le_rfl (by norm_num)

/-- The Möbius weight has absolute value one exactly on the squarefree integers. -/
theorem abs_moebius_eq_one_of_squarefree {d : ℕ} (hd : Squarefree d) :
    |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hd]
  push_cast
  simp [abs_pow]

/-- **The Möbius inverse of the Tatuzawa–Iseki weight has the same critical condition, up to a
constant: its critical condition number is at least `√N/4`.** -/
theorem criticalNorm_moebiusPowerWeight_zero_lower {N : ℕ} (hN : 1 ≤ N) :
    (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) ≤ criticalNorm (moebiusPowerWeight 0) N := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set S := (Finset.Icc 1 N).filter (fun d => Squarefree d) with hSdef
  have hsub : S ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hnn : ∀ d ∈ Finset.Icc 1 N,
      0 ≤ |moebiusPowerWeight 0 d| * (d : ℝ) ^ (-(1 / 2 : ℝ)) := fun d _ =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hpart : ∑ d ∈ S, |moebiusPowerWeight 0 d| * (d : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ criticalNorm (moebiusPowerWeight 0) N :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi _ => hnn i hi
  have hterm : ∀ d ∈ S,
      (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ |moebiusPowerWeight 0 d| * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro d hd
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdN⟩, hsq⟩ := hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hdNR : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
    rw [moebiusPowerWeight_zero, abs_moebius_eq_one_of_squarefree hsq, one_mul]
    exact Real.rpow_le_rpow_of_nonpos hdpos hdNR (by norm_num)
  have hcount : (S.card : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ ∑ d ∈ S, |moebiusPowerWeight 0 d| * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hstep := Finset.card_nsmul_le_sum S
      (fun d => |moebiusPowerWeight 0 d| * (d : ℝ) ^ (-(1 / 2 : ℝ)))
      ((N : ℝ) ^ (-(1 / 2 : ℝ))) hterm
    rwa [nsmul_eq_mul] at hstep
  have hdensity : (N : ℝ) / 4 ≤ (S.card : ℝ) := quarter_le_card_squarefree N
  have hposexp : (0 : ℝ) < (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hlow : (N : ℝ) / 4 * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (S.card : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right hdensity hposexp.le
  have hval : (N : ℝ) / 4 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by
    have hmul : (N : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) = (N : ℝ) ^ (1 / 2 : ℝ) := by
      nth_rewrite 1 [show (N : ℝ) = (N : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    calc (N : ℝ) / 4 * (N : ℝ) ^ (-(1 / 2 : ℝ))
        = (1 / 4 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
      _ = (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by rw [hmul]
  rw [← hval]
  exact le_trans hlow (le_trans hcount hpart)

/-- **The Möbius inverse of the Tatuzawa–Iseki weight is not critically subpower either.** -/
theorem not_criticallySubpower_moebiusPowerWeight_zero :
    ¬ CriticallySubpower (moebiusPowerWeight 0) :=
  not_criticallySubpower_of_powerLower (c := 1 / 2) (c₀ := 1 / 4) (by norm_num) (by norm_num)
    fun _ hN => criticalNorm_moebiusPowerWeight_zero_lower hN

end

end RHTower
