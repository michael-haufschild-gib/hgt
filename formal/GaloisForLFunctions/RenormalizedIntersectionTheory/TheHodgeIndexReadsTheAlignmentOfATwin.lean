import GaloisForLFunctions.HeckeKreinToeplitz.TheSelectiveIndexOfTheAtomicKernelIsOneSquare
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin

/-!
# The Hodge index reads the alignment of a twin

At atomic resolution a sign gauge `ω` (`ω² = 1`) acts on the prime form by congruence,
`P_N ↦ P_N(ω ·)`, so every gauge has the index ladder of `ζ`
(`HeckeKreinToeplitz.hermNegIndex_gaugeAtom_eq`). The renormalized Hodge index is the index on the
pole hyperplane `Σ_{n ≤ N} x_n/√n = 0` (`HeckeKreinToeplitz.poleNegIndex`). It is decided by the
**alignment** of the gauge: the pole moment of the gauge's top vector `ω(n) n^{−1/2}`, which is the
harmonic sum `S_N(ω) = Σ_{n ≤ N} ω(n)/n` (`gaugeHarmonicSum`), against the pole mass
`H_N = Σ_{n ≤ N} 1/n ~ log N`.

* **Small alignment puts the top on the hyperplane** (`exists_twin_top_on_pole_hyperplane`): if
  `S_N(ω)² = o(log N)` (`SmallAlignment`), the top of the twin projected onto the pole hyperplane
  keeps its Rayleigh quotient: `P_N(ωx) ≥ (log N − γ − ε)|x|²` there.
* **Selection** (`eventually_poleNegIndex_window_of_smallAlignment`): in the index-one window
  `log N − γ − 2 log 2 < D < log N − γ` the Hodge index holds for `ζ` (pole index `0`) and fails
  for every gauge of small alignment (pole index `1`).
* **The Liouville twin** (`smallAlignment_liouvilleSign`): `|S_N(λ)| ≤ 2`, so the twin that flips
  every prime has small alignment.

For `ζ` the alignment is total, `S_N(1) = H_N`: the top of the prime form is the pole itself. The
witness is `x = (ω − s) n^{−1/2}`, `s = S_N(ω)/H_N`; its twin `ωx` is the pole minus `s` times the
twin's top, and its cost is read off the ground-state identity polarized at the pole. The finite
flip twins have alignment bounded below by a positive constant; they are separated instead by the
glued test index (`TheGluedIndexSelectsZeta`).
-/

open Finset Filter
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticElectrostatics (atomicWeilForm)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

local notation "γ" => Real.eulerMascheroniConstant

/-- The **harmonic sum** of a gauge, `S_N(ω) = Σ_{n ≤ N} ω(n)/n`: the pole moment of its top. -/
def gaugeHarmonicSum (ω : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, ω n / n

/-- **Small alignment**: `S_N(ω)² = o(log N)`. -/
def SmallAlignment (ω : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → gaugeHarmonicSum ω N ^ 2 ≤ δ * Real.log N

/-- The Liouville twin has bounded harmonic sums, hence small alignment. -/
theorem smallAlignment_liouvilleSign : SmallAlignment liouvilleSign := by
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop |>.eventually_ge_atTop (4 / δ))
  refine ⟨N₀, fun N hN => ?_⟩
  have hL : 4 / δ ≤ Real.log N := hN₀ N hN
  have hS := abs_sum_liouvilleSign_div_le N
  have hS2 : gaugeHarmonicSum liouvilleSign N ^ 2 ≤ 4 := by
    rw [← sq_abs, show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact pow_le_pow_left₀ (abs_nonneg _) hS 2
  have : 4 ≤ δ * Real.log N := by rwa [div_le_iff₀' hδ] at hL
  linarith

/-- Cost of the twin's top in the projection: `s²(L + C)H ≤ S²(1 + C)`, `s = S/H`, `L ≤ H`. -/
theorem cost_pole_le {L H S C : ℝ} (hH : 1 ≤ H) (hLH : L ≤ H) (hC : 0 ≤ C) :
    (S / H) ^ 2 * ((L + C) * H) ≤ S ^ 2 * (1 + C) := by
  have hH0 : 0 < H := by linarith
  have e : (S / H) ^ 2 * ((L + C) * H) = S ^ 2 * ((L + C) / H) := by field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg S)
  rw [div_le_iff₀ hH0]
  linarith [mul_le_mul_of_nonneg_left hH hC]

/-- Cost of the cross term in the projection. -/
theorem cost_cross_le {L H S g B : ℝ} (hH : 1 ≤ H) (hLH : L ≤ H) (hg : 0 ≤ g) :
    2 * (|S / H| * ((L + g) * |S| + B * H)) ≤ 2 * (S ^ 2 * (1 + g)) + (B ^ 2 + S ^ 2) := by
  have hH0 : 0 < H := by linarith
  rw [abs_div, abs_of_pos hH0]
  have e : |S| / H * ((L + g) * |S| + B * H) = S ^ 2 * ((L + g) / H) + B * |S| := by
    rw [← sq_abs S]; field_simp
  rw [e]
  have h1 : (L + g) / H ≤ 1 + g := by
    rw [div_le_iff₀ hH0]
    linarith [mul_le_mul_of_nonneg_left hH hg]
  have h2 : 2 * (B * |S|) ≤ B ^ 2 + S ^ 2 := by
    nlinarith [sq_nonneg (B - |S|), sq_abs S]
  have h3 := mul_le_mul_of_nonneg_left h1 (sq_nonneg S)
  linarith

/-- **The top of a twin of small alignment lies on the pole hyperplane.** For every `ε > 0`,
eventually in `N`, the twin's prime form `P_N(ωx)` reaches `(log N − γ − ε)|x|²` at a nonzero `x`
with `Σ_{n ≤ N} x_n/√n = 0`. -/
theorem exists_twin_top_on_pole_hyperplane {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hA : SmallAlignment ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 ∧
      0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
      (Real.log N - γ - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ atomicWeilForm N (fun n => ω n * x n) := by
  set C₀ := Real.log 4 + 4
  set B := Real.log 4 + 4 + Real.log 2 + γ
  have hC₀ : 0 ≤ C₀ := by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hB : 0 ≤ B := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  set A := 4 + C₀ + 2 * γ
  have hA0 : 0 < A := by positivity
  obtain ⟨N₁, hN₁⟩ := hA (ε / (4 * A)) (by positivity)
  obtain ⟨N₄, hN₄⟩ := hA 1 one_pos
  obtain ⟨N₂, hN₂⟩ := eventually_atomicWeilForm_truncPole_ge (show 0 < ε / 2 by positivity)
  obtain ⟨N₃, hN₃⟩ : ∃ N₃ : ℕ, ∀ N, N₃ ≤ N → γ + ε ≤ Real.log N ∧ 4 * B ^ 2 / ε ≤ Real.log N ∧
      3 ≤ Real.log N := by
    obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop |>.eventually_ge_atTop
        (max (γ + ε) (max (4 * B ^ 2 / ε) 3)))
    exact ⟨N₃, fun N hN => by
      have := hN₃ N hN
      simp only [Function.comp] at this
      exact ⟨(le_max_left _ _).trans this, ((le_max_left _ _).trans (le_max_right _ _)).trans this,
        ((le_max_right _ _).trans (le_max_right _ _)).trans this⟩⟩
  refine ⟨max (max N₁ N₄) (max N₂ N₃), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN4 : N₄ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN3 : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hLγ, hLB, hL3⟩ := hN₃ N hN3
  have hN1' : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    rw [this, Nat.cast_zero, Real.log_zero] at hL3
    linarith
  set b := RenormalizedArithmeticPotentialTheory.truncPole N
  set H := ∑ n ∈ Icc 1 N, (1 : ℝ) / n
  set S := gaugeHarmonicSum ω N
  set L := Real.log N
  have hSδ : S ^ 2 ≤ ε / (4 * A) * L := hN₁ N hN1
  have hS1 : S ^ 2 ≤ 1 * L := hN₄ N hN4
  have hb2 : ∀ n ∈ Icc 1 N, b n ^ 2 = 1 / n := fun n hn => by
    simp only [b, RenormalizedArithmeticPotentialTheory.truncPole, if_pos (mem_Icc.mp hn).2, poleVector_sq]
  have hbsq : ∑ n ∈ Icc 1 N, b n ^ 2 = H := sum_congr rfl hb2
  have hbs : ∀ n ∈ Icc 1 N, b n / Real.sqrt n = 1 / n := fun n hn => by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [b, RenormalizedArithmeticPotentialTheory.truncPole, if_pos (mem_Icc.mp hn).2, poleVector]
    rw [div_div, Real.mul_self_sqrt hn0.le]
  have hHL : L ≤ H := by
    have h := log_add_one_le_harmonic N
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    have : L ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log (by exact_mod_cast hN1') (by linarith)
    simp only [H, one_div]
    linarith
  have hH3 : 3 ≤ H := hL3.trans hHL
  have hH0 : 0 < H := by linarith
  set s := S / H
  -- the witness: the twin's top projected onto the pole hyperplane
  set x : ℕ → ℝ := fun n => (ω n - s) * b n
  have horth : ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 := by
    have : ∀ n ∈ Icc 1 N, x n / Real.sqrt n = ω n / n - s * (1 / n) := fun n hn => by
      rw [show x n / Real.sqrt n = (ω n - s) * (b n / Real.sqrt n) by simp only [x]; ring,
        hbs n hn]
      ring
    rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum]
    show S - s * H = 0
    rw [div_mul_cancel₀ S hH0.ne', sub_self]
  have hxsq : ∑ n ∈ Icc 1 N, x n ^ 2 = H - S ^ 2 / H := by
    have : ∀ n ∈ Icc 1 N, x n ^ 2 = 1 / n - 2 * s * (ω n / n) + s ^ 2 * (1 / n) :=
      fun n hn => by
        have hl := hω n
        simp only [x]
        rw [mul_pow, hb2 n hn]
        have : (ω n - s) ^ 2 = 1 - 2 * s * ω n + s ^ 2 := by linear_combination hl
        rw [this]
        ring
    rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
    show H - 2 * s * S + s ^ 2 * H = H - S ^ 2 / H
    simp only [s]
    field_simp
    ring
  have hxpos : 0 < ∑ n ∈ Icc 1 N, x n ^ 2 := by
    rw [hxsq]
    have : S ^ 2 / H < H := by
      rw [div_lt_iff₀ hH0]
      have := lt_mul_self (show 1 < H by linarith)
      linarith
    linarith
  refine ⟨x, horth, hxpos, ?_⟩
  -- the twin of the witness is the pole minus `s` times the twin's top
  set u : ℕ → ℝ := fun n => -s * (ω n * b n)
  have hlx : (fun n => ω n * x n) = fun n => b n + u n := by
    funext n
    have hl := hω n
    simp only [x, u]
    linear_combination b n * hl
  rw [hlx, atomicWeilForm_truncPole_add N u]
  have hPb : (L - γ - ε / 2) * H ≤ atomicWeilForm N b := by
    have := hN₂ N hN2
    rwa [hbsq] at this
  have hlb2 : ∑ n ∈ Icc 1 N, (ω n * b n) ^ 2 = H := by
    rw [← hbsq]
    exact sum_congr rfl fun n _ => by rw [mul_pow, sq (ω n), hω, one_mul]
  have hPu : -(s ^ 2 * ((L + C₀) * H)) ≤ atomicWeilForm N u := by
    have hu : u = fun n => (-s) * (ω n * b n) := rfl
    rw [hu, atomicWeilForm_smul, neg_sq]
    have hbot := fixedPoint_bottom_ge (κ := -1) (by norm_num) N (fun n => ω n * b n)
    rw [hlb2] at hbot
    have e : ((-1 : ℝ) - 1 / -1) = 0 := by norm_num
    rw [e, zero_mul, zero_add] at hbot
    have : -((L + C₀) * H) ≤ atomicWeilForm N (fun n => ω n * b n) := by
      simp only [L, C₀] at hbot ⊢; linarith
    have := mul_le_mul_of_nonneg_left this (sq_nonneg s)
    linarith
  have hcross : |∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * b n * u n| ≤
      |s| * ((L + γ) * |S| + B * H) := by
    have e : ∀ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * b n * u n =
        -s * ((L - γ) * (ω n / n) +
          (mertensSum (N / n) + Real.log n - (L - γ)) * (ω n * (1 / n))) := by
      intro n hn
      simp only [u]
      have hbb : b n * b n = 1 / n := by rw [← sq, hb2 n hn]
      have : (mertensSum (N / n) + Real.log n) * b n * (-s * (ω n * b n)) =
          -s * ((mertensSum (N / n) + Real.log n) * ω n * (b n * b n)) := by ring
      rw [this, hbb]
      ring
    rw [sum_congr rfl e, ← mul_sum, abs_mul, abs_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
    rw [sum_add_distrib, ← mul_sum]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      have : |L - γ| ≤ L + γ := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    · refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [show B * H = ∑ n ∈ Icc 1 N, B * (1 / (n : ℝ)) by rw [← mul_sum]]
      refine sum_le_sum fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hωn : |ω n| = 1 := abs_eq_one_iff_mul_self_eq_one.mpr (hω n)
      rw [abs_mul, abs_mul, hωn, one_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
      exact mul_le_mul_of_nonneg_right (abs_row_sub_le hn) (by positivity)
  -- the two costs of the projection
  have hT1 : s ^ 2 * ((L + C₀) * H) ≤ S ^ 2 * (1 + C₀) := cost_pole_le (by linarith) hHL hC₀
  have hT2 : 2 * (|s| * ((L + γ) * |S| + B * H)) ≤ 2 * (S ^ 2 * (1 + γ)) + (B ^ 2 + S ^ 2) :=
    cost_cross_le (by linarith) hHL hγ.le
  have hεA : S ^ 2 * A ≤ ε / 4 * H :=
    calc S ^ 2 * A ≤ ε / (4 * A) * L * A := mul_le_mul_of_nonneg_right hSδ hA0.le
      _ = ε / 4 * L := by field_simp
      _ ≤ ε / 4 * H := mul_le_mul_of_nonneg_left hHL (by positivity)
  have hBε : B ^ 2 ≤ ε / 4 * H := by
    have : 4 * B ^ 2 / ε ≤ H := hLB.trans hHL
    rw [div_le_iff₀ hε] at this
    linarith
  have hsum : S ^ 2 * (1 + C₀) + 2 * (S ^ 2 * (1 + γ)) + S ^ 2 = S ^ 2 * A := by
    simp only [A]; ring
  have hxH : ∑ n ∈ Icc 1 N, x n ^ 2 ≤ H := by
    rw [hxsq]
    have : 0 ≤ S ^ 2 / H := div_nonneg (sq_nonneg _) hH0.le
    linarith
  have hcoef : 0 ≤ L - γ - ε := by linarith
  have hcr := (abs_le.mp hcross).1
  calc (L - γ - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ (L - γ - ε) * H :=
        mul_le_mul_of_nonneg_left hxH hcoef
    _ ≤ atomicWeilForm N b + atomicWeilForm N u +
        2 * ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * b n * u n := by
        linarith

/-- A twin of small alignment has a negative direction on the pole hyperplane at every
counterterm below `log N − γ`. -/
theorem eventually_exists_neg_on_pole_of_smallAlignment {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hA : SmallAlignment ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, D < Real.log N - γ - ε →
      ∃ c, poleFunctional N c = 0 ∧ hermQuad ((gaugeAtomMatrix N D ω).map (↑)) c < 0 := by
  obtain ⟨N₀, hN₀⟩ := exists_twin_top_on_pole_hyperplane hω hA hε
  filter_upwards [eventually_ge_atTop N₀] with N hN D hD
  obtain ⟨x, hx, hmass, hge⟩ := hN₀ N hN
  refine ⟨fun n : PrimeHorizonIndex N => (x n : ℂ), ?_, ?_⟩
  · rw [poleFunctional_restrict, hx, Complex.ofReal_zero]
  · rw [hermQuad_gaugeAtom_restrict N D hω]
    nlinarith

/-- **The Hodge index selects `ζ` against every twin of small alignment.** In the index-one window
`log N − γ − 2 log 2 < D < log N − γ`, eventually in `N`, the pole index of `ζ` is `0` and that of
the gauge is `1`. -/
theorem eventually_poleNegIndex_window_of_smallAlignment {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hA : SmallAlignment ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, Real.log N - γ - 2 * Real.log 2 + ε ≤ D → D < Real.log N - γ - ε →
      poleNegIndex N (gram (atomKernel D) (horizonPoint N)) = 0 ∧
        poleNegIndex N ((gaugeAtomMatrix N D ω).map (↑)) = 1 := by
  filter_upwards [eventually_poleNegIndex_window hε,
    eventually_exists_neg_on_pole_of_smallAlignment hω hA hε,
    eventually_hermNegIndex_atom_le_one hε] with N hwin hneg hle D hD₁ hD₂
  refine ⟨(hwin D hD₁ hD₂).1, le_antisymm ?_ ?_⟩
  · exact (poleNegIndex_gauge_bounds N D hω).1.trans (hle D hD₁)
  · obtain ⟨c, hc0, hc⟩ := hneg D hD₂
    exact one_le_negIndexOn (LinearMap.mem_ker.mpr hc0) hc

end GaloisForLFunctions.RenormalizedIntersectionTheory
