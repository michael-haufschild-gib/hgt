import GaloisForLFunctions.RHTower.Matveev.FeldmanSiegelSystem
import GaloisForLFunctions.RHTower.Matveev.IntegerNodeHermite

/-!
# The extrapolation of Fel'dman's auxiliary function

Suppose the true auxiliary values vanish, `Φ_{σ,τ}(x) = 0`, at the nodes `x < X` for all
`σ + |τ| < T`.  Then for `σ + |τ| + M < T` they vanish at every `x < 2X`, provided one numerical
inequality holds.  The step:

* at a node, `|F_{σ′,τ′}(x)| = |F − Φ| ≤ β`, a multiple of `|Λ|`, for all `σ′ + |τ′| < T`, so the
  first `M` derivatives of `f = F_{σ,τ}` along the diagonal are at most `ε = (T + W)^M β`;
* the lossless Hermite–Schwarz bound on the circle `|w| = 8X` gives at `x′ < 2X`
  `|f(x′)| ≤ H + (2/7)^{MX} (G + H)` with `G` the growth of `f` on the circle and `H` the Hermite
  correction, itself a multiple of `ε`;
* `|Φ(x′)| ≤ |f(x′)| + β`, and `B^{|τ|} Φ(x′) = D · A(x′)` with `A(x′) ∈ ℤ`; if
  `B^T |Φ(x′)| < D` then `A(x′) = 0`.

Iterating with `X_r = 2^r X₀` and `T_r = T₀ − rM` gives the extrapolation to `x < 2^R X₀`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset Complex Metric

variable {m : ℕ} {p : Fin (m + 1) → ℕ} {b : Fin (m + 1) → ℤ}

/-- The bound for `|F_{σ,τ}|` on the circle `|w| = ρ`, for `|τ| ≤ T`. -/
def feldmanGrowthBound (m N q T : ℕ) (Cmax W ρ : ℝ) : ℝ :=
  ((N + 1) * q ^ (m + 1) : ℕ) * Cmax * (2 ^ N * (ρ + N + 1) ^ N) * (2 * q : ℝ) ^ T *
    Real.exp (ρ * (2 * q * W))

/-- The bound for `|F_{σ,τ} − Φ_{σ,τ}|` on the disc `|z| ≤ ρ`, for `|τ| ≤ T`. -/
def feldmanErrorBound (m N q T : ℕ) (Cmax Wt ρ lam : ℝ) : ℝ :=
  ((N + 1) * q ^ (m + 1) : ℕ) * Cmax * (2 ^ N * (ρ + N + 1) ^ N) * (2 * q : ℝ) ^ T *
    Real.exp (ρ * (q * Wt)) * (2 * (ρ * q * |lam|))

/-- The bound for `|Φ_{σ,τ}(x′)|`, `x′ < 2X`, produced by one extrapolation step. -/
def feldmanStepBound (m N q T X M : ℕ) (Cmax W Wt lam : ℝ) : ℝ :=
  integerHermiteBound X M (8 * X) (((T : ℝ) + W) ^ M * feldmanErrorBound m N q T Cmax Wt (8 * X) lam) +
    (2 / 7 : ℝ) ^ (M * X) * (feldmanGrowthBound m N q T Cmax W (8 * X) +
      integerHermiteBound X M (8 * X)
        (((T : ℝ) + W) ^ M * feldmanErrorBound m N q T Cmax Wt (8 * X) lam)) +
    feldmanErrorBound m N q T Cmax Wt (8 * X) lam

theorem feldmanErrorBound_nonneg {N q T : ℕ} {Cmax Wt ρ lam : ℝ} (hC : 0 ≤ Cmax) (hρ : 0 ≤ ρ) :
    0 ≤ feldmanErrorBound m N q T Cmax Wt ρ lam := by
  unfold feldmanErrorBound; positivity

theorem feldmanGrowthBound_nonneg {N q T : ℕ} {Cmax W ρ : ℝ} (hC : 0 ≤ Cmax) (hρ : 0 ≤ ρ) :
    0 ≤ feldmanGrowthBound m N q T Cmax W ρ := by
  unfold feldmanGrowthBound; positivity

variable (p b)

/-- The distance `|F − Φ|` on the disc of radius `ρ`. -/
theorem norm_feldmanAux_sub_le (hp : ∀ j, 1 ≤ p j) (hB : 0 < b (Fin.last m))
    (hb : ∀ j, |b j| ≤ b (Fin.last m)) {N q : ℕ} (hq : 1 ≤ q) (C : FeldmanIndex N q m → ℤ)
    {Cmax : ℝ} (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (hCmax : 0 ≤ Cmax) {ρ : ℝ}
    (hΛ : ρ * q * |primeLogForm p b| ≤ 1) {T σ : ℕ} {τ : Fin m → ℕ} (hτ : ∑ j, τ j ≤ T)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    ‖feldmanAux p b N q C σ τ z - feldmanTrueAux p b N q C σ τ z‖ ≤
      feldmanErrorBound m N q T Cmax (totalLogSum p) ρ (primeLogForm p b) := by
  have hW := totalLogSum_nonneg p hp
  have hq1 : (1 : ℝ) ≤ 2 * q := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hzΛ : ‖z‖ * q * |primeLogForm p b| ≤ 1 :=
    le_trans (by gcongr) hΛ
  refine (norm_feldmanAux_sub_feldmanTrueAux_le hB hb hp C hC σ τ hzΛ).trans ?_
  unfold feldmanErrorBound
  have h1 : (2 * q : ℝ) ^ (∑ j, τ j) ≤ (2 * q : ℝ) ^ T := pow_le_pow_right₀ hq1 hτ
  have hρ : 0 ≤ ρ := (norm_nonneg z).trans hz
  gcongr

/-- The growth of `F_{σ,τ}` on the circle of radius `ρ`. -/
theorem norm_feldmanAux_le_growth (hp : ∀ j, 1 ≤ p j) (hB : 0 < b (Fin.last m))
    (hb : ∀ j, |b j| ≤ b (Fin.last m)) {N q : ℕ} (hq : 1 ≤ q) (C : FeldmanIndex N q m → ℤ)
    {Cmax : ℝ} (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (hCmax : 0 ≤ Cmax) {T σ : ℕ} {τ : Fin m → ℕ}
    (hτ : ∑ j, τ j ≤ T) {ρ : ℝ} {w : ℂ} (hw : ‖w‖ = ρ) :
    ‖feldmanAux p b N q C σ τ w‖ ≤ feldmanGrowthBound m N q T Cmax (baseLogSum p) ρ := by
  have hq1 : (1 : ℝ) ≤ 2 * q := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  refine (norm_feldmanAux_le hB hb hp C hC σ τ w).trans ?_
  unfold feldmanGrowthBound
  rw [hw]
  have h1 : (2 * q : ℝ) ^ (∑ j, τ j) ≤ (2 * q : ℝ) ^ T := pow_le_pow_right₀ hq1 hτ
  have hρ : 0 ≤ ρ := hw ▸ norm_nonneg w
  gcongr

/-- **The arithmetic step.**  If `B^T |Φ_{σ,τ}(x)| < D` at a natural number `x` with `σ < S` and
`|τ| ≤ T`, then `Φ_{σ,τ}(x) = 0`. -/
theorem feldmanTrueAux_eq_zero_of_small (hp : ∀ j, 1 ≤ p j) (hB : 0 < b (Fin.last m)) {N q S : ℕ}
    (C : FeldmanIndex N q m → ℤ) {σ T : ℕ} (hσS : σ < S) {τ : Fin m → ℕ} (hτ : ∑ j, τ j ≤ T)
    (x : ℕ)
    (hsmall : (b (Fin.last m) : ℝ) ^ T * ‖feldmanTrueAux p b N q C σ τ (x : ℂ)‖ <
      feldmanDivisor (N + 1) S) :
    feldmanTrueAux p b N q C σ τ (x : ℂ) = 0 := by
  have hp0 : ∀ j, 0 < p j := fun j => hp j
  have hrel := pow_mul_feldmanTrueAux_natCast p b hp0 hB.ne' C hσS τ x
  have hD : (0 : ℝ) < feldmanDivisor (N + 1) S := by exact_mod_cast feldmanDivisor_pos _ _
  have hB1 : (1 : ℝ) ≤ b (Fin.last m) := by exact_mod_cast hB
  have hA : feldmanArith p b N q S C σ τ x = 0 := by
    have hnorm := congrArg norm hrel
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_intCast, Complex.norm_natCast,
      Complex.norm_intCast, abs_of_pos (by exact_mod_cast hB : (0 : ℝ) < b (Fin.last m))] at hnorm
    have hle : (b (Fin.last m) : ℝ) ^ (∑ j, τ j) * ‖feldmanTrueAux p b N q C σ τ (x : ℂ)‖ ≤
        (b (Fin.last m) : ℝ) ^ T * ‖feldmanTrueAux p b N q C σ τ (x : ℂ)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hτ) (norm_nonneg _)
    have hlt : (feldmanDivisor (N + 1) S : ℝ) * |(feldmanArith p b N q S C σ τ x : ℝ)| <
        feldmanDivisor (N + 1) S := by
      rw [← hnorm]; exact hle.trans_lt hsmall
    have habs : |(feldmanArith p b N q S C σ τ x : ℝ)| < 1 := by
      by_contra h
      push Not at h
      nlinarith
    have : |feldmanArith p b N q S C σ τ x| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.mp this
  rw [hA, Int.cast_zero, mul_zero] at hrel
  have hBne : (b (Fin.last m) : ℂ) ^ (∑ j, τ j) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hB.ne')
  exact (mul_eq_zero.mp hrel).resolve_left hBne

/-- **One extrapolation step.** -/
theorem feldman_step (hp : ∀ j, 1 ≤ p j) (hB : 0 < b (Fin.last m))
    (hb : ∀ j, |b j| ≤ b (Fin.last m)) {N q S : ℕ} (hq : 1 ≤ q) (C : FeldmanIndex N q m → ℤ)
    {Cmax : ℝ} (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (hCmax : 0 ≤ Cmax) {X T M : ℕ} (hX : 1 ≤ X)
    (hTS : T ≤ S) (hΛ : 8 * (X : ℝ) * q * |primeLogForm p b| ≤ 1)
    (hzero : ∀ x < X, ∀ σ (τ : Fin m → ℕ), σ + ∑ j, τ j < T →
      feldmanTrueAux p b N q C σ τ (x : ℂ) = 0)
    (hgain : (b (Fin.last m) : ℝ) ^ T * feldmanStepBound m N q T X M Cmax (baseLogSum p)
      (totalLogSum p) (primeLogForm p b) < feldmanDivisor (N + 1) S) :
    ∀ x < 2 * X, ∀ σ (τ : Fin m → ℕ), σ + ∑ j, τ j + M < T →
      feldmanTrueAux p b N q C σ τ (x : ℂ) = 0 := by
  intro x' hx' σ τ hστ
  set W := baseLogSum p with hWdef
  set Wt := totalLogSum p with hWtdef
  set lam := primeLogForm p b with hlamdef
  set ρ : ℝ := 8 * X with hρdef
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hW0 : 0 ≤ W := baseLogSum_nonneg p hp
  set β := feldmanErrorBound m N q T Cmax Wt ρ lam with hβdef
  have hβ0 : 0 ≤ β := feldmanErrorBound_nonneg hCmax hρ0.le
  set ε := ((T : ℝ) + W) ^ M * β with hεdef
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hρΛ : ρ * q * |lam| ≤ 1 := by rw [hρdef]; exact hΛ
  -- the error on the disc
  have herr : ∀ σ' (τ' : Fin m → ℕ), ∑ j, τ' j ≤ T → ∀ z : ℂ, ‖z‖ ≤ ρ →
      ‖feldmanAux p b N q C σ' τ' z - feldmanTrueAux p b N q C σ' τ' z‖ ≤ β :=
    fun σ' τ' hτ' z hz => norm_feldmanAux_sub_le p b hp hB hb hq C hC hCmax hρΛ hτ' hz
  have hT1 : 1 ≤ T := by omega
  -- the values at the nodes
  have hnode : ∀ x < X, ∀ σ' (τ' : Fin m → ℕ), σ' + ∑ j, τ' j ≤ T - 1 →
      ‖feldmanAux p b N q C σ' τ' (x : ℂ)‖ ≤ β := by
    intro x hx σ' τ' h
    have h0 := hzero x hx σ' τ' (by omega)
    have hxρ : ‖(x : ℂ)‖ ≤ ρ := by
      rw [Complex.norm_natCast, hρdef]
      have : (x : ℝ) ≤ X := by exact_mod_cast hx.le
      linarith
    have := herr σ' τ' (by omega) (x : ℂ) hxρ
    rwa [h0, sub_zero] at this
  -- the jets at the nodes
  have hjet : ∀ x < X, ∀ t < M,
      ‖iteratedDeriv t (feldmanAux p b N q C σ τ) (x : ℂ)‖ ≤ ε := by
    intro x hx t ht
    have h := norm_iteratedDeriv_feldmanAux_le p b hp C (n := T - 1) (β := β)
      (fun σ' τ' h' => hnode x hx σ' τ' h') t σ τ (by omega)
    have hbase : ((T - 1 : ℕ) : ℝ) + W ≤ (T : ℝ) + W := by
      have : ((T - 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast Nat.sub_le T 1
      linarith
    have hT1' : (1 : ℝ) ≤ (T : ℝ) + W := by
      have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
      linarith
    calc _ ≤ (((T - 1 : ℕ) : ℝ) + W) ^ t * β := h
      _ ≤ ((T : ℝ) + W) ^ t * β :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase t) hβ0
      _ ≤ ((T : ℝ) + W) ^ M * β :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1' ht.le) hβ0
  -- Hermite–Schwarz
  set f := feldmanAux p b N q C σ τ with hfdef
  have hf : Differentiable ℂ f := differentiable_feldmanAux p b C σ τ
  set Hb := integerHermiteBound X M ρ ε with hHbdef
  have hH : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖hermiteCorrection f (natNodes X) M z‖ ≤ Hb :=
    fun z hz => norm_hermiteCorrection_natNodes_le hε0 hρ0.le hjet hz
  have hτT : ∑ j, τ j ≤ T := by omega
  set G := feldmanGrowthBound m N q T Cmax W ρ with hGdef
  have hbd : ∀ w ∈ sphere (0 : ℂ) ρ, ‖f w - hermiteCorrection f (natNodes X) M w‖ ≤ G + Hb := by
    intro w hw
    have hw' : ‖w‖ = ρ := by simpa using hw
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hH w hw'.le))
    exact norm_feldmanAux_le_growth p b hp hB hb hq C hC hCmax hτT hw'
  have hXρ : (X : ℝ) ≤ ρ := by rw [hρdef]; linarith
  have h7 : ρ - X = 7 * X := by rw [hρdef]; ring
  have hDpos : 0 < (ρ - X) ^ (M * X) := by rw [h7]; positivity
  have hDlow : ∀ w ∈ sphere (0 : ℂ) ρ, (ρ - X) ^ (M * X) ≤ ‖hermiteNodePoly (natNodes X) M w‖ :=
    fun w hw => le_norm_hermiteNodePoly_natNodes M hXρ (by simpa using hw)
  have hx'ρ : ‖(x' : ℂ)‖ ≤ ρ := by
    rw [Complex.norm_natCast, hρdef]
    have : (x' : ℝ) ≤ 2 * X := by exact_mod_cast hx'.le
    linarith
  have hschwarz := norm_le_hermiteSchwarz hf (natNodes X) M hρ0 hDpos hbd hDlow
    (z := (x' : ℂ)) (by simpa using hx'ρ)
  have hΩ : ‖hermiteNodePoly (natNodes X) M (x' : ℂ)‖ ≤ ((2 * X : ℕ) : ℝ) ^ (M * X) :=
    norm_hermiteNodePoly_natNodes_le (by omega) M hx'
  have hratio : ((2 * X : ℕ) : ℝ) ^ (M * X) / (ρ - X) ^ (M * X) = (2 / 7 : ℝ) ^ (M * X) := by
    rw [h7, ← div_pow]
    congr 1
    push_cast
    field_simp
  have hGH : 0 ≤ G + Hb := add_nonneg (feldmanGrowthBound_nonneg hCmax hρ0.le)
    (integerHermiteBound_nonneg X M hε0)
  have hfx : ‖f (x' : ℂ)‖ ≤ Hb + (2 / 7 : ℝ) ^ (M * X) * (G + Hb) := by
    refine hschwarz.trans (add_le_add (hH _ hx'ρ) ?_)
    calc ‖hermiteNodePoly (natNodes X) M (x' : ℂ)‖ * ((G + Hb) / (ρ - X) ^ (M * X))
        ≤ ((2 * X : ℕ) : ℝ) ^ (M * X) * ((G + Hb) / (ρ - X) ^ (M * X)) :=
          mul_le_mul_of_nonneg_right hΩ (div_nonneg hGH hDpos.le)
      _ = ((2 * X : ℕ) : ℝ) ^ (M * X) / (ρ - X) ^ (M * X) * (G + Hb) := by ring
      _ = (2 / 7 : ℝ) ^ (M * X) * (G + Hb) := by rw [hratio]
  -- the true value
  have hΦ : ‖feldmanTrueAux p b N q C σ τ (x' : ℂ)‖ ≤
      feldmanStepBound m N q T X M Cmax W Wt lam := by
    have h1 := herr σ τ hτT (x' : ℂ) hx'ρ
    have h2 : ‖feldmanTrueAux p b N q C σ τ (x' : ℂ)‖ ≤ ‖f (x' : ℂ)‖ +
        ‖feldmanAux p b N q C σ τ (x' : ℂ) - feldmanTrueAux p b N q C σ τ (x' : ℂ)‖ := by
      have := norm_sub_le (f (x' : ℂ))
        (feldmanAux p b N q C σ τ (x' : ℂ) - feldmanTrueAux p b N q C σ τ (x' : ℂ))
      simpa [hfdef] using this
    unfold feldmanStepBound
    rw [← hρdef, ← hβdef, ← hεdef, ← hHbdef, ← hGdef]
    linarith
  have hσS : σ < S := by omega
  refine feldmanTrueAux_eq_zero_of_small p b hp hB C hσS hτT x' ?_
  have hB0 : (0 : ℝ) ≤ (b (Fin.last m) : ℝ) ^ T := by
    have : (0 : ℝ) < b (Fin.last m) := by exact_mod_cast hB
    positivity
  exact (mul_le_mul_of_nonneg_left hΦ hB0).trans_lt hgain

/-- **The extrapolation.**  From vanishing at `x < X₀` for `σ + |τ| < T₀`, after `R` steps the true
auxiliary values vanish at `x < 2^R X₀` for `σ + |τ| < T₀ − RM`. -/
theorem feldman_extrapolation (hp : ∀ j, 1 ≤ p j) (hB : 0 < b (Fin.last m))
    (hb : ∀ j, |b j| ≤ b (Fin.last m)) {N q S : ℕ} (hq : 1 ≤ q) (C : FeldmanIndex N q m → ℤ)
    {Cmax : ℝ} (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (hCmax : 0 ≤ Cmax) {X₀ T₀ M R : ℕ}
    (hX₀ : 1 ≤ X₀) (hT₀S : T₀ ≤ S) (hRM : R * M < T₀)
    (hΛ : 8 * ((2 ^ R * X₀ : ℕ) : ℝ) * q * |primeLogForm p b| ≤ 1)
    (h0 : ∀ x < X₀, ∀ σ (τ : Fin m → ℕ), σ + ∑ j, τ j < T₀ →
      feldmanTrueAux p b N q C σ τ (x : ℂ) = 0)
    (hgain : ∀ r < R, (b (Fin.last m) : ℝ) ^ (T₀ - r * M) *
      feldmanStepBound m N q (T₀ - r * M) (2 ^ r * X₀) M Cmax (baseLogSum p) (totalLogSum p)
        (primeLogForm p b) < feldmanDivisor (N + 1) S) :
    ∀ x < 2 ^ R * X₀, ∀ σ (τ : Fin m → ℕ), σ + ∑ j, τ j < T₀ - R * M →
      feldmanTrueAux p b N q C σ τ (x : ℂ) = 0 := by
  have hΛnn : 0 ≤ |primeLogForm p b| := abs_nonneg _
  suffices H : ∀ r ≤ R, ∀ x < 2 ^ r * X₀, ∀ σ (τ : Fin m → ℕ), σ + ∑ j, τ j < T₀ - r * M →
      feldmanTrueAux p b N q C σ τ (x : ℂ) = 0 from H R le_rfl
  intro r
  induction r with
  | zero => intro _; simpa using h0
  | succ r ih =>
      intro hr x hx σ τ hστ
      have hrR : r < R := by omega
      have hXr : 1 ≤ 2 ^ r * X₀ := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hpow : 2 ^ r * X₀ ≤ 2 ^ R * X₀ :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hrR.le)
      have hΛr : 8 * ((2 ^ r * X₀ : ℕ) : ℝ) * q * |primeLogForm p b| ≤ 1 := by
        refine le_trans ?_ hΛ
        have : ((2 ^ r * X₀ : ℕ) : ℝ) ≤ ((2 ^ R * X₀ : ℕ) : ℝ) := by exact_mod_cast hpow
        gcongr
      have hrM : r * M + M ≤ R * M := by
        have := Nat.mul_le_mul_right M (show r + 1 ≤ R by omega)
        linarith [Nat.succ_mul r M]
      have step := feldman_step p b hp hB hb hq C hC hCmax (X := 2 ^ r * X₀) (T := T₀ - r * M)
        (M := M) hXr (by omega) (by exact_mod_cast hΛr) (ih (Nat.le_of_succ_le hr)) (hgain r hrR)
      refine step x (by rw [pow_succ] at hx; linarith) σ τ ?_
      have : (r + 1) * M = r * M + M := Nat.succ_mul r M
      omega

end GaloisForLFunctions.RHTower.Matveev
