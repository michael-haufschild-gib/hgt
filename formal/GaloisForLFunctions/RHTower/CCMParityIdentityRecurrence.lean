import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Sum- and difference-frequency Gram matrices at identity recurrence

Let a finite top layer `σ_j = t_j + iδ` (`δ > 0`) carry multiplicities `M_j > 0`. On `[−a, a]` the
families `c_j = cos(t_jx)sinh(δx)` and `s_j = sin(t_jx)sinh(δx)` have Gram matrices proportional, to
leading order in `a`, to `B(a) + C(a)` and `B(a) − C(a)`, where

* `B_{jk}(a) = 2√(M_jM_k)·Re(e^{i(t_j−t_k)a}/(2δ + i(t_j−t_k)))` (difference frequencies),
* `C_{jk}(a) = 2√(M_jM_k)·Re(e^{i(t_j+t_k)a}/(2δ + i(t_j+t_k)))` (sum frequencies).

**Rayleigh comparison** (`quadForm_sub_add_le_quadForm_abs_add`). For matrices `B, C` with
nonnegative entries and every vector `v`,
`vᵀ(B−C)v + 2Σ_j v_j²·min(B_jj, C_jj) ≤ |v|ᵀ(B+C)|v|`.

**Identity recurrence** (`exists_aperture_ccmGap`). For every finite top layer there are arbitrarily
large apertures `a` at which all phases `t_j a` are close to `2πℤ`. There every entry of `B(a)` and
`C(a)` is positive, so for every unit `v` the unit vector `|v|` gives
`vᵀ(B−C)v + c₀ ≤ |v|ᵀ(B+C)|v|` with `c₀ = min_j M_jδ/(4δ² + 4t_j²) > 0`, independent of `a`.
No independence of the top ordinates is needed: the recurrence point `0` is reached by simultaneous
Dirichlet approximation for any frequencies.

**Sector comparison in a Hilbert space** (`odd_beats_even`). If two finite families `f` and `g`
have Gram matrices satisfying the comparison above, then every `u` has Bessel sum
`Σ⟨u, f_j⟩² ≤ Λ‖u‖²`, where `Λ` is the top Gram value of `f` (frame bound), while the test vector
`u₀ = Σ|v₀_j|g_j` has `Σ⟨u₀, g_j⟩² ≥ (Λ + 2c)‖u₀‖²` (Cauchy–Schwarz).

These statements compare the `s`- and `c`-families only. In the restricted Weil form an odd source
`u` receives `M_j(⟨u,d_j⟩² − ⟨u,c_j⟩²)` from the quartet of `σ_j`, with `d_j = sin(t_jx)cosh(δx)`, so
the comparison of the parity sectors also involves the cross Gram `⟨c_j, d_k⟩`, whose
difference-frequency part `Im(e^{i(t_k−t_j)a}/(2δ + i(t_k−t_j)))` is not small at identity
recurrence.
-/

open Real Finset

noncomputable section

namespace RHTower

/-! ## The Rayleigh comparison -/

/-- **Rayleigh comparison.** For matrices with nonnegative entries,
`vᵀ(B−C)v + 2Σ_j v_j² min(B_jj, C_jj) ≤ |v|ᵀ(B+C)|v|`. -/
theorem quadForm_sub_add_le_quadForm_abs_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B C : ι → ι → ℝ) (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) (v : ι → ℝ) :
    ∑ i, ∑ j, v i * v j * (B i j - C i j) + 2 * ∑ i, v i ^ 2 * min (B i i) (C i i) ≤
      ∑ i, ∑ j, |v i| * |v j| * (B i j + C i j) := by
  have hdiag : 2 * ∑ i, v i ^ 2 * min (B i i) (C i i) =
      ∑ i, ∑ j, if i = j then 2 * v i ^ 2 * min (B i i) (C i i) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    ring
  rw [hdiag, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with hij
  · subst hij
    have hm : min (B i i) (C i i) ≤ C i i := min_le_right _ _
    have hv : |v i| * |v i| = v i ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
    rw [hv]
    have h2 : 0 ≤ v i ^ 2 := sq_nonneg _
    nlinarith
  · have h1 : v i * v j * (B i j - C i j) ≤ |v i * v j| * |B i j - C i j| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |B i j - C i j| ≤ B i j + C i j := by
      rw [abs_le]; constructor <;> linarith [hB i j, hC i j]
    rw [add_zero, ← abs_mul]
    calc v i * v j * (B i j - C i j) ≤ |v i * v j| * |B i j - C i j| := h1
      _ ≤ |v i * v j| * (B i j + C i j) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

/-- With a uniform lower bound `c ≤ min(B_jj, C_jj)`, unit vectors gain at least `2c`. -/
theorem quadForm_sub_add_two_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B C : ι → ι → ℝ) (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) {c : ℝ}
    (hc : ∀ i, c ≤ min (B i i) (C i i)) (v : ι → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    ∑ i, ∑ j, v i * v j * (B i j - C i j) + 2 * c ≤
      ∑ i, ∑ j, |v i| * |v j| * (B i j + C i j) := by
  have h := quadForm_sub_add_le_quadForm_abs_add B C hB hC v
  have h2 : c ≤ ∑ i, v i ^ 2 * min (B i i) (C i i) := by
    calc c = ∑ i, v i ^ 2 * c := by rw [← Finset.sum_mul, hv, one_mul]
      _ ≤ ∑ i, v i ^ 2 * min (B i i) (C i i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hc i) (sq_nonneg _)
  linarith

/-! ## The boundary Gram entries -/

/-- `Re(e^{iψ}/(2δ + iT)) = (2δ cos ψ + T sin ψ)/(4δ² + T²)`. -/
def gramEntry (δ T ψ : ℝ) : ℝ := (2 * δ * Real.cos ψ + T * Real.sin ψ) / (4 * δ ^ 2 + T ^ 2)

/-- Near a multiple of `2π` the entry is at least half its value at `0`. -/
theorem gramEntry_ge_of_near {δ T ψ : ℝ} (hδ : 0 < δ) (n : ℤ)
    (hψ : |ψ - 2 * π * n| ≤ δ / (2 * (|T| + 1))) (hψ1 : |ψ - 2 * π * n| ≤ 1 / 2) :
    δ / (4 * δ ^ 2 + T ^ 2) ≤ gramEntry δ T ψ := by
  unfold gramEntry
  set x := ψ - 2 * π * n with hx
  have hcos : Real.cos ψ = Real.cos x := by
    rw [hx, show ψ - 2 * π * n = ψ + ((-n : ℤ) : ℝ) * (2 * π) by push_cast; ring,
      Real.cos_add_int_mul_two_pi]
  have hsin : Real.sin ψ = Real.sin x := by
    rw [hx, show ψ - 2 * π * n = ψ + ((-n : ℤ) : ℝ) * (2 * π) by push_cast; ring,
      Real.sin_add_int_mul_two_pi]
  rw [hcos, hsin]
  have hT1 : 0 < |T| + 1 := by positivity
  have hxδ : |x| ≤ δ / 2 := by
    refine le_trans hψ ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg T]
  have hxT : |T| * |x| ≤ δ / 2 := by
    have : |x| * (2 * (|T| + 1)) ≤ δ := by rwa [le_div_iff₀ (by positivity)] at hψ
    nlinarith [abs_nonneg x, abs_nonneg T]
  have hcosx : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hsinx : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
  have hδ1 : δ / 2 ≤ δ := by linarith
  have hx2 : x ^ 2 ≤ |x| * (δ / 2) := by
    rw [← sq_abs]; nlinarith [abs_nonneg x]
  have hden : 0 < 4 * δ ^ 2 + T ^ 2 := by positivity
  rw [div_le_div_iff_of_pos_right hden]
  have h1 : T * Real.sin x ≥ -(|T| * |x|) := by
    have := abs_mul T (Real.sin x)
    have h3 : |T * Real.sin x| ≤ |T| * |x| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hsinx (abs_nonneg T)
    linarith [neg_abs_le (T * Real.sin x)]
  have h2 : 2 * δ * (1 - x ^ 2 / 2) ≤ 2 * δ * Real.cos x := by
    exact mul_le_mul_of_nonneg_left hcosx (by linarith)
  have hx14 : x ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg x]
  have h3 : δ * x ^ 2 ≤ δ / 4 := by nlinarith
  nlinarith [abs_nonneg x]

/-- The difference-frequency Gram matrix `B(a)`. -/
def ccmGramB {m : ℕ} (t M : Fin m → ℝ) (δ a : ℝ) (j k : Fin m) : ℝ :=
  2 * Real.sqrt (M j * M k) * gramEntry δ (t j - t k) ((t j - t k) * a)

/-- The sum-frequency Gram matrix `C(a)`. -/
def ccmGramC {m : ℕ} (t M : Fin m → ℝ) (δ a : ℝ) (j k : Fin m) : ℝ :=
  2 * Real.sqrt (M j * M k) * gramEntry δ (t j + t k) ((t j + t k) * a)

/-! ## Recurrence to the identity -/

/-- **Simultaneous recurrence.** For any frequencies, arbitrarily large apertures put every phase
`t_j a` within `ε` of `2πℤ`. -/
theorem exists_aperture_near_lattice {m : ℕ} (t : Fin m → ℝ) {ε : ℝ} (hε : 0 < ε) {A₀ : ℝ}
    (hA₀ : 0 < A₀) : ∃ a : ℝ, A₀ ≤ a ∧ ∀ j, ∃ n : ℤ, |t j * a - 2 * π * n| < ε := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt (2 * π / ε)
  have hQpos : 0 < Q := by
    have : (0 : ℝ) < Q := lt_trans (by positivity) hQ
    exact_mod_cast this
  obtain ⟨q, hq1, -, hq⟩ := GaloisForLFunctions.HTGeometry.exists_simultaneous_dirichlet
    (fun j => t j * A₀ / (2 * π)) hQpos
  refine ⟨q * A₀, ?_, fun j => ?_⟩
  · have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    nlinarith
  · obtain ⟨p, hp⟩ := hq j
    refine ⟨p, ?_⟩
    have hpi : 0 < 2 * π := by positivity
    have e : t j * (q * A₀) - 2 * π * p = 2 * π * ((q : ℝ) * (t j * A₀ / (2 * π)) - p) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hpi]
    have hQε : 2 * π / Q < ε := by
      have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQpos
      rw [div_lt_iff₀ hQ0]
      rw [div_lt_iff₀ hε] at hQ
      linarith
    calc 2 * π * |(q : ℝ) * (t j * A₀ / (2 * π)) - p| < 2 * π * (1 / Q) := by gcongr
      _ = 2 * π / Q := by ring
      _ < ε := hQε

/-! ## The odd sector wins at identity recurrence -/

theorem gramEntry_pos_of_near {δ T ψ : ℝ} (hδ : 0 < δ) (n : ℤ)
    (hψ : |ψ - 2 * π * n| ≤ δ / (2 * (|T| + 1))) (hψ1 : |ψ - 2 * π * n| ≤ 1 / 2) :
    0 < gramEntry δ T ψ :=
  lt_of_lt_of_le (by positivity) (gramEntry_ge_of_near hδ n hψ hψ1)

/-- **Identity recurrence beats the even sector.** For any top layer `(t_j, M_j)` with `δ > 0` and
any `c ≤ 2M_jδ/(4δ² + 4t_j²)` for all `j`, there are arbitrarily large apertures `a` such that every
unit vector `v` satisfies `vᵀ(B(a) − C(a))v + 2c ≤ |v|ᵀ(B(a) + C(a))|v|`. -/
theorem exists_aperture_ccmGap {m : ℕ} (t M : Fin m → ℝ) (hM : ∀ j, 0 < M j) {δ : ℝ}
    (hδ : 0 < δ) {c : ℝ} (hc : ∀ j, c ≤ 2 * M j * (δ / (4 * δ ^ 2 + (2 * t j) ^ 2)))
    {A₀ : ℝ} (hA₀ : 0 < A₀) :
    ∃ a : ℝ, A₀ ≤ a ∧ ∀ v : Fin m → ℝ, ∑ i, v i ^ 2 = 1 →
      ∑ i, ∑ j, v i * v j * (ccmGramB t M δ a i j - ccmGramC t M δ a i j) + 2 * c ≤
        ∑ i, ∑ j, |v i| * |v j| * (ccmGramB t M δ a i j + ccmGramC t M δ a i j) := by
  set τ : ℝ := ∑ j, |t j| with hτ
  have hτ0 : 0 ≤ τ := Finset.sum_nonneg fun j _ => abs_nonneg _
  have htj : ∀ j, |t j| ≤ τ := fun j =>
    Finset.single_le_sum (f := fun j => |t j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  set ε : ℝ := min (δ / (2 * (2 * τ + 1))) (1 / 2) / 2 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨a, ha, hnear⟩ := exists_aperture_near_lattice t hε0 hA₀
  choose n hn using hnear
  refine ⟨a, ha, fun v hv => ?_⟩
  -- every combined phase is within `2ε` of the lattice
  have hsum : ∀ j k, |(t j + t k) * a - 2 * π * (((n j + n k : ℤ)) : ℝ)| ≤ 2 * ε := by
    intro j k
    have h1 := hn j
    have h2 := hn k
    have e : (t j + t k) * a - 2 * π * (((n j + n k : ℤ)) : ℝ) =
        (t j * a - 2 * π * n j) + (t k * a - 2 * π * n k) := by push_cast; ring
    rw [e]
    linarith [abs_add_le (t j * a - 2 * π * n j) (t k * a - 2 * π * n k)]
  have hdiff : ∀ j k, |(t j - t k) * a - 2 * π * (((n j - n k : ℤ)) : ℝ)| ≤ 2 * ε := by
    intro j k
    have h1 := hn j
    have h2 := hn k
    have e : (t j - t k) * a - 2 * π * (((n j - n k : ℤ)) : ℝ) =
        (t j * a - 2 * π * n j) - (t k * a - 2 * π * n k) := by push_cast; ring
    rw [e]
    linarith [abs_sub (t j * a - 2 * π * n j) (t k * a - 2 * π * n k)]
  have hεle1 : 2 * ε ≤ 1 / 2 := by
    rw [hε]; linarith [min_le_right (δ / (2 * (2 * τ + 1))) (1 / 2)]
  have hεleδ : ∀ T : ℝ, |T| ≤ 2 * τ → 2 * ε ≤ δ / (2 * (|T| + 1)) := by
    intro T hT
    have h1 : 2 * ε ≤ δ / (2 * (2 * τ + 1)) := by
      rw [hε]; linarith [min_le_left (δ / (2 * (2 * τ + 1))) (1 / 2)]
    refine le_trans h1 ?_
    apply div_le_div_of_nonneg_left hδ.le (by positivity)
    linarith
  have hTsum : ∀ j k, |t j + t k| ≤ 2 * τ := fun j k => by
    linarith [abs_add_le (t j) (t k), htj j, htj k]
  have hTdiff : ∀ j k, |t j - t k| ≤ 2 * τ := fun j k => by
    linarith [abs_sub (t j) (t k), htj j, htj k]
  have hB : ∀ i j, 0 ≤ ccmGramB t M δ a i j := by
    intro i j
    unfold ccmGramB
    have := (gramEntry_pos_of_near hδ _ (le_trans (hdiff i j) (hεleδ _ (hTdiff i j)))
      (le_trans (hdiff i j) hεle1)).le
    positivity
  have hC : ∀ i j, 0 ≤ ccmGramC t M δ a i j := by
    intro i j
    unfold ccmGramC
    have := (gramEntry_pos_of_near hδ _ (le_trans (hsum i j) (hεleδ _ (hTsum i j)))
      (le_trans (hsum i j) hεle1)).le
    positivity
  have hdiag : ∀ i, c ≤ min (ccmGramB t M δ a i i) (ccmGramC t M δ a i i) := by
    intro i
    have hsq : Real.sqrt (M i * M i) = M i := Real.sqrt_mul_self (hM i).le
    have hBi : ccmGramB t M δ a i i = M i / δ := by
      unfold ccmGramB gramEntry
      rw [hsq, sub_self, zero_mul, Real.cos_zero, Real.sin_zero]
      field_simp
      ring
    have hCi : 2 * M i * (δ / (4 * δ ^ 2 + (2 * t i) ^ 2)) ≤ ccmGramC t M δ a i i := by
      unfold ccmGramC
      rw [hsq]
      have hp := hsum i i
      have hT := hTsum i i
      have hge := gramEntry_ge_of_near hδ _ (le_trans hp (hεleδ _ hT)) (le_trans hp hεle1)
      rw [show t i + t i = 2 * t i by ring] at hge ⊢
      have hM0 : 0 ≤ 2 * M i := by linarith [hM i]
      exact mul_le_mul_of_nonneg_left hge hM0
    refine le_min ?_ (le_trans (hc i) hCi)
    rw [hBi]
    refine le_trans (hc i) ?_
    have hden : 4 * δ ^ 2 ≤ 4 * δ ^ 2 + (2 * t i) ^ 2 := by nlinarith [sq_nonneg (2 * t i)]
    have h1 : δ / (4 * δ ^ 2 + (2 * t i) ^ 2) ≤ δ / (4 * δ ^ 2) :=
      div_le_div_of_nonneg_left hδ.le (by positivity) hden
    have h2 : 2 * M i * (δ / (4 * δ ^ 2)) = M i / δ / 2 := by field_simp; ring
    have hMi := hM i
    have h3 : M i / δ / 2 ≤ M i / δ := by
      have : 0 ≤ M i / δ := by positivity
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * M i)]
  exact quadForm_sub_add_two_mul_le _ _ hB hC hdiag v hv

/-! ## The sector comparison in a Hilbert space -/

section Bessel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

/-- The Bessel sum `Σ_j ⟨u, f_j⟩²` of a finite family. -/
def besselSum (f : Fin m → E) (u : E) : ℝ := ∑ j, (inner ℝ u (f j)) ^ 2

theorem norm_sq_sum_smul_eq (f : Fin m → E) (w : Fin m → ℝ) :
    ‖∑ j, w j • f j‖ ^ 2 = ∑ j, ∑ k, w j * w k * inner ℝ (f j) (f k) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- **Frame bound.** If `‖Σ w_j f_j‖² ≤ Λ Σ w_j²` for all `w`, then `Σ_j ⟨u, f_j⟩² ≤ Λ‖u‖²`. -/
theorem besselSum_le_of_frame (f : Fin m → E) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ w : Fin m → ℝ, ‖∑ j, w j • f j‖ ^ 2 ≤ Λ * ∑ j, w j ^ 2) (u : E) :
    besselSum f u ≤ Λ * ‖u‖ ^ 2 := by
  set c : Fin m → ℝ := fun j => inner ℝ u (f j) with hc
  set S : ℝ := ∑ j, c j ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hSeq : S = inner ℝ u (∑ j, c j • f j) := by
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right, hc, sq]
  have h1 : S ≤ ‖u‖ * ‖∑ j, c j • f j‖ := by rw [hSeq]; exact real_inner_le_norm _ _
  have h2 := hΛ c
  have hsq : S ^ 2 ≤ ‖u‖ ^ 2 * (Λ * S) := by
    have h3 : S ^ 2 ≤ (‖u‖ * ‖∑ j, c j • f j‖) ^ 2 := by
      exact pow_le_pow_left₀ hS0 h1 2
    rw [mul_pow] at h3
    calc S ^ 2 ≤ ‖u‖ ^ 2 * ‖∑ j, c j • f j‖ ^ 2 := h3
      _ ≤ ‖u‖ ^ 2 * (Λ * S) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  show S ≤ Λ * ‖u‖ ^ 2
  rcases hS0.lt_or_eq with hpos | hzero
  · have : S * S ≤ S * (Λ * ‖u‖ ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this hpos
  · rw [← hzero]
    exact mul_nonneg hΛ0 (sq_nonneg _)

/-- **The test vector.** For `u = Σ_j w_j g_j`, `‖u‖⁴ ≤ (Σ_j w_j²)·Σ_j ⟨u, g_j⟩²`. -/
theorem norm_pow_four_le_besselSum (g : Fin m → E) (w : Fin m → ℝ) :
    ‖∑ j, w j • g j‖ ^ 4 ≤ (∑ j, w j ^ 2) * besselSum g (∑ j, w j • g j) := by
  set u := ∑ j, w j • g j with hu
  have h1 : ‖u‖ ^ 2 = ∑ j, w j * inner ℝ u (g j) := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => rw [hu]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w (fun j => inner ℝ u (g j))
  rw [← h1] at h2
  unfold besselSum
  calc ‖u‖ ^ 4 = (‖u‖ ^ 2) ^ 2 := by ring
    _ ≤ _ := h2

/-- **Odd beats even, abstract form.** Let `f, g` be finite families with
`Σ v_jv_k⟨f_j,f_k⟩ + 2c ≤ Σ \|v_j\|\|v_k\|⟨g_j,g_k⟩` for every unit `v`, `c > 0`, and let `v₀` be a unit
vector maximising `Σ v_jv_k⟨f_j,f_k⟩` with value `Λ`. Then every `u` has `Σ⟨u,f_j⟩² ≤ Λ‖u‖²`, while
`u₀ = Σ\|v₀_j\|g_j` is nonzero with `Σ⟨u₀,g_j⟩² ≥ (Λ + 2c)‖u₀‖²`. -/
theorem odd_beats_even (f g : Fin m → E) {c : ℝ} (hc : 0 < c)
    (hcmp : ∀ v : Fin m → ℝ, ∑ j, v j ^ 2 = 1 →
      ∑ j, ∑ k, v j * v k * inner ℝ (f j) (f k) + 2 * c ≤
        ∑ j, ∑ k, |v j| * |v k| * inner ℝ (g j) (g k))
    {v₀ : Fin m → ℝ} (hv₀ : ∑ j, v₀ j ^ 2 = 1)
    (hmax : ∀ v : Fin m → ℝ, ∑ j, v j ^ 2 = 1 →
      ∑ j, ∑ k, v j * v k * inner ℝ (f j) (f k) ≤ ∑ j, ∑ k, v₀ j * v₀ k * inner ℝ (f j) (f k)) :
    (∀ u : E, besselSum f u ≤ (∑ j, ∑ k, v₀ j * v₀ k * inner ℝ (f j) (f k)) * ‖u‖ ^ 2) ∧
      (∑ j, |v₀ j| • g j ≠ 0) ∧
      ((∑ j, ∑ k, v₀ j * v₀ k * inner ℝ (f j) (f k)) + 2 * c) * ‖∑ j, |v₀ j| • g j‖ ^ 2 ≤
        besselSum g (∑ j, |v₀ j| • g j) := by
  set Λ := ∑ j, ∑ k, v₀ j * v₀ k * inner ℝ (f j) (f k) with hΛdef
  -- the frame constant of `f` is `Λ`, by homogeneity
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef, ← norm_sq_sum_smul_eq]; exact sq_nonneg _
  have hframe : ∀ w : Fin m → ℝ, ‖∑ j, w j • f j‖ ^ 2 ≤ Λ * ∑ j, w j ^ 2 := by
    intro w
    rw [norm_sq_sum_smul_eq]
    have hr0 : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (w j)
    rcases hr0.lt_or_eq with hpos | hzero
    · obtain ⟨σ, hσ0, hσσ⟩ : ∃ σ : ℝ, 0 < σ ∧ σ * σ = ∑ j, w j ^ 2 :=
        ⟨Real.sqrt _, Real.sqrt_pos.mpr hpos, Real.mul_self_sqrt hpos.le⟩
      have hunit : ∑ j, (w j / σ) ^ 2 = 1 := by
        simp only [div_pow]
        rw [← Finset.sum_div, sq σ, hσσ, div_self hpos.ne']
      have := hmax (fun j => w j / σ) hunit
      have e : ∑ j, ∑ k, (w j / σ) * (w k / σ) * inner ℝ (f j) (f k) =
          (∑ j, ∑ k, w j * w k * inner ℝ (f j) (f k)) / ∑ j, w j ^ 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hσσ]; field_simp
      rw [e, div_le_iff₀ hpos] at this
      linarith
    · have hw0 : ∀ j, w j = 0 := by
        intro j
        have h1 : w j ^ 2 ≤ ∑ j, w j ^ 2 := Finset.single_le_sum (f := fun j => w j ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ j)
        have h2 : w j ^ 2 ≤ 0 := by linarith
        nlinarith [sq_nonneg (w j)]
      simp [hw0]
  refine ⟨fun u => besselSum_le_of_frame f hΛ0 hframe u, ?_, ?_⟩
  · intro h0
    have hcmp0 := hcmp v₀ hv₀
    have hn := norm_sq_sum_smul_eq g (fun j => |v₀ j|)
    rw [h0, norm_zero] at hn
    linarith
  · set u := ∑ j, |v₀ j| • g j with hu
    have hunit : ∑ j, |v₀ j| ^ 2 = 1 := by simp only [sq_abs]; exact hv₀
    have h4 := norm_pow_four_le_besselSum g (fun j => |v₀ j|)
    rw [hunit, one_mul] at h4
    have hn := norm_sq_sum_smul_eq g (fun j => |v₀ j|)
    have hcmp0 := hcmp v₀ hv₀
    have hge : Λ + 2 * c ≤ ‖u‖ ^ 2 := by rw [hu, hn]; linarith
    calc (Λ + 2 * c) * ‖u‖ ^ 2 ≤ ‖u‖ ^ 2 * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hge (sq_nonneg _)
      _ = ‖u‖ ^ 4 := by ring
      _ ≤ besselSum g u := h4

end Bessel

end RHTower

end
