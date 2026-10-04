import GaloisForLFunctions.HTGeometry.SmoothedPerronFormula
import GaloisForLFunctions.HTGeometry.VerticalContourShift

/-!
# Counting with a holomorphic continuation: the smoothed Perron contour shift

Let `|c(n)| ≤ 1`, `c(0) = 0`, and suppose `L(c, s) = H(s)/(s − 1)` on `Re s > 1` with `H`
holomorphic on `Re s > a`.  Fix `a < σ₀ < 1` and assume

* on the strip `σ₀ ≤ Re s ≤ 3/2`, `|H(s)/(s − 1)| ≤ K |Im s|^{κ₁}` for `|Im s| ≥ T₀`, with `κ₁ < 2`;
* on the line `Re s = σ₀`, `|H(s)/(s − 1)| ≤ K₀ (|t| + 1)^θ` with `0 ≤ θ < 1`.

Then for every `κ > 0`, `Σ_{n ≤ X} c(n) = H(1) X + O(X^{(θ + σ₀)/(1 + θ) + κ})`
(`exists_norm_sum_sub_le`).

**Proof.**  Smooth the cutoff with `Smooth1 ν ε` (PNTPlus): the smoothed sum is the Perron
integral on `Re s = 3/2` (`verticalIntegral'_eq_tsum_smooth1`).  Shift it to `Re s = σ₀` past the
simple pole at `1` with residue `H(1) 𝓜[Smooth1](1) X` (`tsum_smooth1_eq_residue_add`).  The
Mellin transform satisfies `|𝓜(s)| ≤ 4/|s|` (`norm_mellin_smooth1_le`) and `≤ C/(ε|s|²)`; their
geometric mean bounds the left line by `X^{σ₀} ε^{−λ}` for any `θ < λ ≤ 1`
(`exists_norm_verticalIntegral'_le`).  The smoothing costs `O(εX + 1)` (`norm_sum_sub_tsum_smooth1_le`)
and `𝓜(1) = 1 + O(ε)`.  Take `ε = X^{−(1−σ₀)/(1+θ)}`.
-/

open Set Function Filter Complex Real MeasureTheory Topology Asymptotics
open scoped Interval

local notation (name := smoothedShiftMellin) "𝓜" => mellin

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SmoothedPerron

variable {ν : ℝ → ℝ}

/-! ## Bounds for the smoothing -/

/-- `|𝓜[Smooth1 ν ε](s)| ≤ 4/|s|` for `0 < Re s ≤ 2`. -/
theorem norm_mellin_smooth1_le (diffν : ContDiff ℝ 1 ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2) (mass_one : ∫ (x : ℝ) in Ioi 0, ν x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_le_one : ε ≤ 1) {s : ℂ} (hs : 0 < s.re) (hs2 : s.re ≤ 2) :
    ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ 4 / ‖s‖ := by
  rw [MellinOfSmooth1a diffν suppν εpos hs, norm_mul, norm_inv, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (norm_nonneg _))
  have hint : IntegrableOn (fun x : ℝ => ν x / x) (Ioi 0) := by
    by_contra h
    rw [integral_undef h] at mass_one
    norm_num at mass_one
  have hes : 0 ≤ ε * s.re := by positivity
  have hes2 : ε * s.re ≤ 2 := by nlinarith
  unfold mellin
  calc ‖∫ x in Ioi (0 : ℝ), (x : ℂ) ^ ((ε : ℂ) * s - 1) • (ν x : ℂ)‖
      ≤ ∫ x in Ioi (0 : ℝ), 4 * (ν x / x) := by
        refine norm_integral_le_of_norm_le (hint.const_mul 4) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : (0 : ℝ) < x := hx
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
          Real.norm_eq_abs]
        have hre : ((ε : ℂ) * s - 1).re = ε * s.re - 1 := by simp
        rw [hre]
        by_cases hν : ν x = 0
        · simp [hν]
        have hmem : x ∈ Icc (1 / 2 : ℝ) 2 := suppν hν
        rw [abs_of_nonneg (νpos x hx0), Real.rpow_sub_one hx0.ne']
        have h1 : x ^ (ε * s.re) ≤ 4 := by
          calc x ^ (ε * s.re) ≤ (2 : ℝ) ^ (ε * s.re) :=
                Real.rpow_le_rpow hx0.le hmem.2 hes
            _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hes2
            _ = 4 := by norm_num
        have h2 : 0 ≤ ν x / x := div_nonneg (νpos x hx0) hx0.le
        calc x ^ (ε * s.re) / x * ν x = x ^ (ε * s.re) * (ν x / x) := by ring
          _ ≤ 4 * (ν x / x) := mul_le_mul_of_nonneg_right h1 h2
    _ = 4 := by rw [integral_const_mul, mass_one, mul_one]

/-- **Unsmoothing.**  Replacing the sharp cutoff `n ≤ X` by `Smooth1 ν ε (n/X)` changes a sum of
coefficients of size `≤ 1` by at most `3εX + 2`. -/
theorem norm_sum_sub_tsum_smooth1_le (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2) (mass_one : ∫ (x : ℝ) in Ioi 0, ν x / x = 1)
    (c : ℕ → ℂ) (hc0 : c 0 = 0) (hc : ∀ n, ‖c n‖ ≤ 1) {X : ℝ} (hX : 0 < X) {ε : ℝ}
    (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    ‖∑ n ∈ Finset.Iic ⌊X⌋₊, c n - ∑' n, c n * Smooth1 ν ε (n / X)‖ ≤ 3 * ε * X + 2 := by
  obtain ⟨c₁, -, hc₁, h₁⟩ := Smooth1Properties_below suppν mass_one
  obtain ⟨c₂, -, hc₂, h₂⟩ := Smooth1Properties_above suppν
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set a : ℝ := X * (1 - c₁ * ε) with ha
  set b : ℝ := X * (1 + c₂ * ε) with hb
  have ha0 : 0 ≤ a := by
    rw [ha, hc₁]; apply mul_nonneg hX.le; nlinarith
  have hab : b - a = 3 * Real.log 2 * ε * X := by rw [ha, hb, hc₁, hc₂]; ring
  have hXb : X < b := by
    rw [hb, hc₂]
    have : 0 < X * (2 * Real.log 2 * ε) := by positivity
    linarith
  set N : ℕ := ⌊b⌋₊ + 1 with hN
  have hvan : ∀ n, n ∉ Finset.range N → c n * Smooth1 ν ε (n / X) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt, hN] at hn
    have hnb : b ≤ n := by
      have := Nat.lt_floor_add_one b
      have h' : ((⌊b⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h'
      linarith
    have : 1 + c₂ * ε ≤ (n : ℝ) / X := by
      rw [le_div_iff₀ hX]; rw [hb] at hnb; linarith
    rw [h₂ ε _ ⟨εpos, ε_lt_one⟩ this]; simp
  rw [tsum_eq_sum hvan]
  have hsplit : ∑ n ∈ Finset.Iic ⌊X⌋₊, c n =
      ∑ n ∈ Finset.range N, (if n ≤ ⌊X⌋₊ then c n else 0) := by
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_Iic, Finset.mem_filter, Finset.mem_range, hN]
    have : ⌊X⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hXb.le
    constructor
    · intro h; exact ⟨by omega, h⟩
    · exact fun h => h.2
  rw [hsplit, ← Finset.sum_sub_distrib]
  set g : ℕ → ℝ := fun n => if a < n ∧ (n : ℝ) < b then 1 else 0 with hg
  have hterm : ∀ n, ‖(if n ≤ ⌊X⌋₊ then c n else 0) - c n * Smooth1 ν ε (n / X)‖ ≤ g n := by
    intro n
    have hg0 : 0 ≤ g n := by simp only [hg]; split_ifs <;> norm_num
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0, hg0]
    have hx : 0 < (n : ℝ) / X := div_pos (by exact_mod_cast hn) hX
    have hrw : (if n ≤ ⌊X⌋₊ then c n else 0) - c n * Smooth1 ν ε (n / X) =
        c n * ((if n ≤ ⌊X⌋₊ then 1 else 0) - Smooth1 ν ε (n / X)) := by
      split_ifs <;> ring
    rw [hrw]
    by_cases hna : (n : ℝ) ≤ a
    · have hle : n ≤ ⌊X⌋₊ := Nat.le_floor (by rw [ha] at hna; nlinarith)
      have hs1 : Smooth1 ν ε (n / X) = 1 := h₁ ε _ εpos hx (by
        rw [div_le_iff₀ hX]; rw [ha] at hna; linarith)
      simp [hle, hs1, hg0]
    by_cases hnb : b ≤ (n : ℝ)
    · have hle : ¬ n ≤ ⌊X⌋₊ := by
        intro h
        have := (Nat.le_floor_iff hX.le).mp h
        linarith
      have hs0 : Smooth1 ν ε (n / X) = 0 := h₂ ε _ ⟨εpos, ε_lt_one⟩ (by
        rw [le_div_iff₀ hX]; rw [hb] at hnb; linarith)
      simp [hle, hs0, hg0]
    have hgn : g n = 1 := by rw [hg]; simp only; rw [if_pos ⟨by linarith, by linarith⟩]
    rw [hgn, norm_mul]
    have hS0 := Smooth1Nonneg νpos hx εpos
    have hS1 := Smooth1LeOne νpos mass_one εpos hx
    have hd : ‖((if n ≤ ⌊X⌋₊ then 1 else 0 : ℝ) - Smooth1 ν ε (n / X) : ℂ)‖ ≤ 1 := by
      rw [show ((if n ≤ ⌊X⌋₊ then 1 else 0 : ℝ) - Smooth1 ν ε (n / X) : ℂ) =
        (((if n ≤ ⌊X⌋₊ then 1 else 0 : ℝ) - Smooth1 ν ε (n / X) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_le]
      split_ifs <;> constructor <;> linarith
    have hd' : ‖((if n ≤ ⌊X⌋₊ then (1 : ℂ) else 0) - (Smooth1 ν ε (n / X) : ℂ))‖ ≤ 1 := by
      convert hd using 2; split_ifs <;> simp
    calc ‖c n‖ * ‖((if n ≤ ⌊X⌋₊ then (1 : ℂ) else 0) - (Smooth1 ν ε (n / X) : ℂ))‖
        ≤ 1 * 1 := mul_le_mul (hc n) hd' (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hcount : ∑ n ∈ Finset.range N, g n ≤ b - a + 2 := by
    rw [hg, Finset.sum_boole]
    have hsubI : (Finset.range N).filter (fun n : ℕ => a < n ∧ (n : ℝ) < b) ⊆
        Finset.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
      intro n hn
      rw [Finset.mem_filter] at hn
      rw [Finset.mem_Ioo]
      exact ⟨(Nat.floor_lt ha0).mpr hn.2.1, Nat.lt_ceil.mpr hn.2.2⟩
    have hcard := Finset.card_le_card hsubI
    rw [Nat.card_Ioo] at hcard
    have hab' : a ≤ b := by
      have : 0 ≤ 3 * Real.log 2 * ε * X := by positivity
      linarith
    have hfc : ⌊a⌋₊ ≤ ⌈b⌉₊ := (Nat.floor_le_floor hab').trans (Nat.floor_le_ceil b)
    have hnat : ((Finset.range N).filter (fun n : ℕ => a < n ∧ (n : ℝ) < b)).card + ⌊a⌋₊ ≤
        ⌈b⌉₊ := by omega
    have hreal : (((Finset.range N).filter (fun n : ℕ => a < n ∧ (n : ℝ) < b)).card : ℝ) +
        ⌊a⌋₊ ≤ ⌈b⌉₊ := by exact_mod_cast hnat
    have hc1 : (⌈b⌉₊ : ℝ) < b + 1 := Nat.ceil_lt_add_one (by linarith)
    have hf1 : a - 1 < (⌊a⌋₊ : ℝ) := Nat.sub_one_lt_floor a
    linarith
  calc ‖∑ n ∈ Finset.range N, ((if n ≤ ⌊X⌋₊ then c n else 0) - c n * Smooth1 ν ε (n / X))‖
      ≤ ∑ n ∈ Finset.range N, g n := norm_sum_le_of_le _ fun n _ => hterm n
    _ ≤ b - a + 2 := hcount
    _ ≤ 3 * ε * X + 2 := by
        rw [hab]
        have : 0 ≤ ε * X := by positivity
        nlinarith

/-! ## The contour shift -/

/-- The smoothed Perron integrand `H(s)/(s − 1) · 𝓜[Smooth1 ν ε](s) · X^s`. -/
def perronIntegrand (ν : ℝ → ℝ) (H : ℂ → ℂ) (ε X : ℝ) (s : ℂ) : ℂ :=
  H s / (s - 1) * 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s

/-- A difference quotient of a function differentiable at `p` is bounded near `p`. -/
theorem isBigO_div_sub_div {G : ℂ → ℂ} {p : ℂ} (hG : DifferentiableAt ℂ G p) :
    ((fun s => G s / (s - p)) - fun s => G p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have h := (hasDerivAt_iff_tendsto_slope.mp hG.hasDerivAt).isBigO_one ℂ
  refine h.congr' (Eventually.of_forall fun s => ?_) (Eventually.of_forall fun s => rfl)
  simp only [slope_def_field, Pi.sub_apply]
  ring

/-- `σ₀ (|Im s| + 1) ≤ 2 |s|` when `0 < σ₀ ≤ min(1, Re s)`. -/
theorem mul_abs_im_add_one_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ ≤ 1) {s : ℂ} (hs : σ₀ ≤ s.re) :
    σ₀ * (|s.im| + 1) ≤ 2 * ‖s‖ := by
  have hre := Complex.abs_re_le_norm s
  have him := Complex.abs_im_le_norm s
  have hab : |s.re| = s.re := abs_of_pos (by linarith)
  have hi0 := abs_nonneg s.im
  nlinarith

/-- `|L(c, s)| ≤ Σ n^{−3/2}` on `Re s = 3/2` for `|c(n)| ≤ 1`. -/
theorem norm_LSeries_le_of_re {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ 1) {s : ℂ} (hs : s.re = 3 / 2) :
    ‖LSeries c s‖ ≤ ∑' n, ‖LSeries.term c (3 / 2 : ℂ) n‖ := by
  have hsum : LSeriesSummable c (3 / 2 : ℂ) :=
    LSeriesSummable_of_le_const_mul_rpow (x := 1) (by norm_num)
      ⟨1, fun n _ => by simpa using hc n⟩
  have heq : ∀ n, ‖LSeries.term c s n‖ = ‖LSeries.term c (3 / 2 : ℂ) n‖ := fun n => by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs]; norm_num
  unfold LSeries
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr heq))
  exact hsum.norm.congr fun n => (heq n).symm

/-- **The contour shift.**  The smoothed sum is the residue at `s = 1` plus the Perron integral
on the line `Re s = σ₀`. -/
theorem tsum_smooth1_eq_residue_add (diffν : ContDiff ℝ 1 ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2) (mass_one : ∫ (x : ℝ) in Ioi 0, ν x / x = 1)
    (c : ℕ → ℂ) (hc0 : c 0 = 0) (hc : ∀ n, ‖c n‖ ≤ 1)
    {H : ℂ → ℂ} {a σ₀ : ℝ} (ha : a < σ₀) (hσ₀ : 0 < σ₀) (hσ₀1 : σ₀ < 1)
    (hH : DifferentiableOn ℂ H {s | a < s.re})
    (hLS : ∀ s : ℂ, 1 < s.re → H s / (s - 1) = LSeries c s)
    {K T₀ κ₁ : ℝ} (hκ₁ : κ₁ < 2)
    (hstrip : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 3 / 2 → T₀ ≤ |s.im| →
      ‖H s / (s - 1)‖ ≤ K * |s.im| ^ κ₁)
    {K₀ θ : ℝ} (hθ : θ < 1)
    (hleft : ∀ t : ℝ, ‖H (σ₀ + t * I) / (σ₀ + t * I - 1)‖ ≤ K₀ * (|t| + 1) ^ θ)
    {X : ℝ} (hX : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    ∑' n, c n * Smooth1 ν ε (n / X) =
      H 1 * 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X +
        VerticalIntegral' (perronIntegrand ν H ε X) σ₀ := by
  obtain ⟨C₂, hC₂, hM₂⟩ := MellinOfSmooth1b diffν suppν
  set M := 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) with hMdef
  set f := perronIntegrand ν H ε X with hfdef
  have hMd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ M s := fun s hs =>
    Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩ νpos mass_one hs
  have hHd : ∀ s : ℂ, a < s.re → DifferentiableAt ℂ H s := fun s hs =>
    hH.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have hXd : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => (X : ℂ) ^ s) s := fun s =>
    differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hX.ne'))
  have hfd : ∀ s : ℂ, a < s.re → 0 < s.re → s ≠ 1 → DifferentiableAt ℂ f s := by
    intro s hs hs0 hs1
    have h1 : DifferentiableAt ℂ (fun s : ℂ => H s / (s - 1)) s :=
      (hHd s hs).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1)
    exact (h1.mul (hMd s hs0)).mul (hXd s)
  have hnormX : ∀ s : ℂ, ‖(X : ℂ) ^ s‖ = X ^ s.re := fun s =>
    Complex.norm_cpow_eq_rpow_re_of_pos hX s
  -- Perron at `3/2`
  have hP := verticalIntegral'_eq_tsum_smooth1 diffν νpos suppν mass_one c hc0 hc hX εpos
    ε_lt_one (σ := 3 / 2) (by norm_num) (by norm_num)
  have hright_eq : VerticalIntegral' f (3 / 2) =
      VerticalIntegral' (fun s => LSeries c s * M s * (X : ℂ) ^ s) (3 / 2) := by
    simp only [VerticalIntegral', VerticalIntegral]
    congr 3
    funext t
    simp only [hfdef, perronIntegrand]
    rw [hLS _ (by simp; norm_num)]
  -- holomorphy off the pole
  have hhol : HolomorphicOn f (Set.Icc σ₀ (3 / 2) ×ℂ Set.univ \ {1}) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    rw [Complex.mem_reProdIm] at hs1
    exact (hfd s (by linarith [hs1.1.1]) (by linarith [hs1.1.1]) hs2).differentiableWithinAt
  -- the pole at `1`
  have hpole : (f - fun s => H 1 * M 1 * (X : ℂ) / (s - 1)) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
    have hG : DifferentiableAt ℂ (fun s => H s * M s * (X : ℂ) ^ s) 1 :=
      ((hHd 1 (by simp; linarith)).mul (hMd 1 (by simp))).mul (hXd 1)
    have h := isBigO_div_sub_div hG
    refine h.congr' (Eventually.of_forall fun s => ?_) (Eventually.of_forall fun s => rfl)
    simp only [Pi.sub_apply, hfdef, perronIntegrand, Complex.cpow_one]
    ring
  -- horizontal decay
  set T₁ : ℝ := max T₀ 1 with hT₁
  set Mb : ℝ → ℝ := fun T => K * C₂ * (X ^ σ₀ + X ^ (3 / 2 : ℝ)) / ε * |T| ^ (κ₁ - 2) with hMb
  have hhor : ∀ T : ℝ, T₁ ≤ |T| → ∀ u ∈ Ι σ₀ (3 / 2), ‖f (u + T * I)‖ ≤ Mb T := by
    intro T hT u hu
    rw [uIoc_of_le (by linarith)] at hu
    have hT1 : 1 ≤ |T| := le_trans (le_max_right _ _) hT
    have hTT₀ : T₀ ≤ |T| := le_trans (le_max_left _ _) hT
    set s : ℂ := (u : ℂ) + T * I with hs
    have hsre : s.re = u := by simp [hs]
    have hsim : s.im = T := by simp [hs]
    have hF := hstrip s (by rw [hsre]; exact hu.1.le) (by rw [hsre]; exact hu.2)
      (by rw [hsim]; exact hTT₀)
    rw [hsim] at hF
    have hMs := hM₂ σ₀ hσ₀ s (by rw [hsre]; exact hu.1.le) (by rw [hsre]; linarith [hu.2]) ε
      εpos ε_lt_one
    have hsT : |T| ≤ ‖s‖ := by rw [← hsim]; exact Complex.abs_im_le_norm s
    have hT0 : 0 < |T| := by linarith
    have hMs' : ‖M s‖ ≤ C₂ / ε * |T| ^ (-2 : ℝ) := by
      refine hMs.trans ?_
      rw [Real.rpow_neg hT0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        mul_inv, div_eq_mul_inv, mul_assoc]
      gcongr
    have hXs : ‖(X : ℂ) ^ s‖ ≤ X ^ σ₀ + X ^ (3 / 2 : ℝ) := by
      rw [hnormX, hsre]
      rcases le_or_gt 1 X with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h hu.2
        have := Real.rpow_nonneg hX.le σ₀
        linarith
      · have := Real.rpow_le_rpow_of_exponent_ge hX h.le hu.1.le
        have := Real.rpow_nonneg hX.le (3 / 2 : ℝ)
        linarith
    have hKT : 0 ≤ K * |T| ^ κ₁ := (norm_nonneg _).trans hF
    calc ‖f s‖ = ‖H s / (s - 1)‖ * ‖M s‖ * ‖(X : ℂ) ^ s‖ := by
          show ‖H s / (s - 1) * M s * (X : ℂ) ^ s‖ = _
          rw [norm_mul, norm_mul]
      _ ≤ (K * |T| ^ κ₁) * (C₂ / ε * |T| ^ (-2 : ℝ)) * (X ^ σ₀ + X ^ (3 / 2 : ℝ)) := by
          gcongr
      _ = Mb T := by
          rw [hMb]
          simp only
          rw [show κ₁ - 2 = κ₁ + (-2) by ring, Real.rpow_add hT0]
          ring
  have hMbt : Tendsto (fun T : ℝ => Mb T * |3 / 2 - σ₀|) atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => Mb T * |3 / 2 - σ₀|) atBot (𝓝 0) := by
    have hp : Tendsto (fun y : ℝ => y ^ (κ₁ - 2)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := 2 - κ₁) (by linarith)
      simpa [neg_sub] using this
    constructor
    · have := ((hp.comp tendsto_abs_atTop_atTop).const_mul
        (K * C₂ * (X ^ σ₀ + X ^ (3 / 2 : ℝ)) / ε)).mul_const |3 / 2 - σ₀|
      simpa [hMb] using this
    · have := ((hp.comp tendsto_abs_atBot_atTop).const_mul
        (K * C₂ * (X ^ σ₀ + X ^ (3 / 2 : ℝ)) / ε)).mul_const |3 / 2 - σ₀|
      simpa [hMb] using this
  have htop : Tendsto (fun y : ℝ => ∫ x in σ₀..(3 / 2 : ℝ), f ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hMbt.1
    filter_upwards [eventually_ge_atTop T₁] with T hT
    have hT' : T₁ ≤ |T| := le_trans hT (le_abs_self T)
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => hhor T hT' u hu
  have hbot : Tendsto (fun y : ℝ => ∫ x in σ₀..(3 / 2 : ℝ), f ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hMbt.2
    filter_upwards [eventually_le_atBot (-T₁)] with T hT
    have hT' : T₁ ≤ |T| := by rw [abs_of_neg (by linarith [le_max_right T₀ 1])]; linarith
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => hhor T hT' u hu
  -- integrability on the left line
  have hleftInt : Integrable fun y : ℝ => f ((σ₀ : ℂ) + (y : ℂ) * I) := by
    have hbase : Integrable fun y : ℝ => (1 + |y|) ^ (-(2 - θ)) := by
      have h : Integrable fun y : ℝ => (1 + ‖y‖) ^ (-(2 - θ)) :=
        integrable_one_add_norm (by simp; linarith)
      exact h.congr (Eventually.of_forall fun y => by simp only [Real.norm_eq_abs])
    refine (hbase.const_mul (K₀ * (4 * C₂ / (ε * σ₀ ^ 2)) * X ^ σ₀)).mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun y => ?_)
      have hne : (σ₀ : ℂ) + (y : ℂ) * I ≠ 1 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      exact ContinuousAt.comp (g := f) (hfd _ (by simp; linarith) (by simp; linarith)
        hne).continuousAt (by fun_prop)
    · filter_upwards with y
      set s : ℂ := (σ₀ : ℂ) + (y : ℂ) * I with hs
      have hsre : s.re = σ₀ := by simp [hs]
      have hsim : s.im = y := by simp [hs]
      have hF := hleft y
      have hMs := hM₂ σ₀ hσ₀ s (by rw [hsre]) (by rw [hsre]; linarith) ε εpos ε_lt_one
      have hlow := mul_abs_im_add_one_le hσ₀ hσ₀1.le (s := s) (by rw [hsre])
      rw [hsim] at hlow
      have hy1 : 0 < |y| + 1 := by positivity
      have hMs' : ‖M s‖ ≤ 4 * C₂ / (ε * σ₀ ^ 2) * ((|y| + 1) ^ 2)⁻¹ := by
        refine hMs.trans ?_
        have hsq : σ₀ ^ 2 * (|y| + 1) ^ 2 ≤ 4 * ‖s‖ ^ 2 := by
          have := mul_self_le_mul_self (by positivity) hlow
          nlinarith
        rw [show 4 * C₂ / (ε * σ₀ ^ 2) * ((|y| + 1) ^ 2)⁻¹ =
          C₂ * (ε * (σ₀ ^ 2 * (|y| + 1) ^ 2 / 4))⁻¹ by field_simp]
        gcongr
        linarith
      have hK₀ : 0 ≤ K₀ * (|y| + 1) ^ θ := (norm_nonneg _).trans hF
      have hpow : (|y| + 1) ^ θ * ((|y| + 1) ^ 2)⁻¹ = (1 + |y|) ^ (-(2 - θ)) := by
        rw [add_comm (|y|) 1, show -(2 - θ) = θ - 2 by ring, Real.rpow_sub (by positivity),
          Real.rpow_two, div_eq_mul_inv]
      calc ‖f s‖ = ‖H s / (s - 1)‖ * ‖M s‖ * ‖(X : ℂ) ^ s‖ := by
            show ‖H s / (s - 1) * M s * (X : ℂ) ^ s‖ = _
            rw [norm_mul, norm_mul]
        _ ≤ (K₀ * (|y| + 1) ^ θ) * (4 * C₂ / (ε * σ₀ ^ 2) * ((|y| + 1) ^ 2)⁻¹) * X ^ σ₀ := by
            rw [hnormX, hsre]
            gcongr
        _ = K₀ * (4 * C₂ / (ε * σ₀ ^ 2)) * X ^ σ₀ * (1 + |y|) ^ (-(2 - θ)) := by
            rw [← hpow]; ring
  -- integrability on the right line
  have hrightInt : Integrable fun y : ℝ => f (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    have hMint := SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν mass_one εpos
      ε_lt_one (σ := 3 / 2) (by norm_num) (by norm_num)
    refine (hMint.norm.const_mul ((∑' n, ‖LSeries.term c (3 / 2 : ℂ) n‖) *
      X ^ (3 / 2 : ℝ))).mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun y => ?_)
      have hne : (((3 / 2 : ℝ) : ℂ)) + (y : ℂ) * I ≠ 1 := by
        intro h; have := congrArg Complex.re h; simp at this; norm_num at this
      exact ContinuousAt.comp (g := f) (hfd _ (by simp; linarith) (by simp)
        hne).continuousAt (by fun_prop)
    · filter_upwards with y
      set s : ℂ := (((3 / 2 : ℝ) : ℂ)) + (y : ℂ) * I with hs
      have hsre : s.re = 3 / 2 := by simp [hs]
      have hfs : f s = LSeries c s * M s * (X : ℂ) ^ s := by
        simp only [hfdef, perronIntegrand]; rw [hLS s (by rw [hsre]; norm_num)]
      rw [hfs, norm_mul, norm_mul, hnormX, hsre]
      have hL := norm_LSeries_le_of_re hc hsre
      calc ‖LSeries c s‖ * ‖M s‖ * X ^ (3 / 2 : ℝ)
          ≤ (∑' n, ‖LSeries.term c (3 / 2 : ℂ) n‖) * ‖M s‖ * X ^ (3 / 2 : ℝ) := by gcongr
        _ = (∑' n, ‖LSeries.term c (3 / 2 : ℂ) n‖) * X ^ (3 / 2 : ℝ) * ‖M s‖ := by ring
        _ = _ := by
            congr 2
  have hshift := verticalIntegral'_sub_of_simple_pole (σ := σ₀) (σ' := 3 / 2) (p := 1)
    (A := H 1 * M 1 * (X : ℂ)) (f := f) (by simp; exact hσ₀1) (by simp; norm_num) hhol hpole
    hbot htop hleftInt hrightInt
  rw [← hP, ← hright_eq]
  linear_combination hshift

/-! ## The left line -/

/-- Geometric interpolation of two upper bounds. -/
theorem le_rpow_mul_rpow {m p q l : ℝ} (hm : 0 ≤ m) (hp : m ≤ p) (hq : m ≤ q) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) : m ≤ p ^ (1 - l) * q ^ l := by
  have h1 : m = m ^ (1 - l) * m ^ l := by
    rw [← Real.rpow_add' hm (by norm_num), sub_add_cancel, Real.rpow_one]
  calc m = m ^ (1 - l) * m ^ l := h1
    _ ≤ p ^ (1 - l) * q ^ l :=
        mul_le_mul (Real.rpow_le_rpow hm hp (by linarith)) (Real.rpow_le_rpow hm hq hl0)
          (Real.rpow_nonneg hm _) (Real.rpow_nonneg (hm.trans hp) _)

theorem interp_rpow_eq {P Q ε u l : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hε : 0 < ε) (hu : 0 < u) :
    (P * u ^ (-1 : ℝ)) ^ (1 - l) * (Q * ε ^ (-1 : ℝ) * u ^ (-2 : ℝ)) ^ l =
      P ^ (1 - l) * Q ^ l * ε ^ (-l) * u ^ (-1 - l) := by
  rw [Real.mul_rpow hP (by positivity), Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hQ (by positivity), ← Real.rpow_mul hu.le, ← Real.rpow_mul hε.le,
    ← Real.rpow_mul hu.le]
  have : u ^ (-1 * (1 - l)) * u ^ (-2 * l) = u ^ (-1 - l) := by
    rw [← Real.rpow_add hu]; congr 1; ring
  rw [show -1 * l = -l by ring]
  calc P ^ (1 - l) * u ^ (-1 * (1 - l)) * (Q ^ l * ε ^ (-l) * u ^ (-2 * l))
      = P ^ (1 - l) * Q ^ l * ε ^ (-l) * (u ^ (-1 * (1 - l)) * u ^ (-2 * l)) := by ring
    _ = _ := by rw [this]

/-- **The left line.**  For `θ < λ ≤ 1`, the Perron integral on `Re s = σ₀` is
`O(X^{σ₀} ε^{−λ})`. -/
theorem exists_norm_verticalIntegral'_le (diffν : ContDiff ℝ 1 ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2) (mass_one : ∫ (x : ℝ) in Ioi 0, ν x / x = 1)
    {H : ℂ → ℂ} {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ₀1 : σ₀ < 1) {K₀ θ : ℝ}
    (hleft : ∀ t : ℝ, ‖H (σ₀ + t * I) / (σ₀ + t * I - 1)‖ ≤ K₀ * (|t| + 1) ^ θ)
    {l : ℝ} (hθl : θ < l) (hl1 : l ≤ 1) (hl0 : 0 ≤ l) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℝ, 0 < X → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖VerticalIntegral' (perronIntegrand ν H ε X) σ₀‖ ≤ B * X ^ σ₀ * ε ^ (-l) := by
  obtain ⟨C₂, hC₂, hM₂⟩ := MellinOfSmooth1b diffν suppν
  have hK₀ : 0 ≤ K₀ := by
    have := (norm_nonneg _).trans (hleft 0)
    simpa using this
  set P : ℝ := 8 / σ₀ with hPdef
  set Q : ℝ := 4 * C₂ / σ₀ ^ 2 with hQdef
  have hP : 0 ≤ P := by positivity
  have hQ : 0 ≤ Q := by positivity
  set r : ℝ := 1 + l - θ with hr
  have hbase : Integrable fun t : ℝ => (1 + |t|) ^ (-r) := by
    have h : Integrable fun y : ℝ => (1 + ‖y‖) ^ (-r) :=
      integrable_one_add_norm (by simp; linarith)
    exact h.congr (Eventually.of_forall fun y => by simp only [Real.norm_eq_abs])
  set Ir : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-r) with hIr
  have hIr0 : 0 ≤ Ir := integral_nonneg fun t => by positivity
  refine ⟨K₀ * P ^ (1 - l) * Q ^ l * Ir, by positivity, fun X hX ε εpos ε_lt_one => ?_⟩
  set f := perronIntegrand ν H ε X with hfdef
  have hpt : ∀ t : ℝ, ‖f ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤
      K₀ * P ^ (1 - l) * Q ^ l * X ^ σ₀ * ε ^ (-l) * (1 + |t|) ^ (-r) := by
    intro t
    set s : ℂ := (σ₀ : ℂ) + (t : ℂ) * I with hs
    have hsre : s.re = σ₀ := by simp [hs]
    have hsim : s.im = t := by simp [hs]
    set u : ℝ := |t| + 1 with hu
    have hu0 : 0 < u := by positivity
    have hlow := mul_abs_im_add_one_le hσ₀ hσ₀1.le (s := s) (by rw [hsre])
    rw [hsim] at hlow
    have hs0 : 0 < ‖s‖ := by
      have := Complex.abs_re_le_norm s; rw [hsre, abs_of_pos hσ₀] at this; linarith
    have hM1 : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ P * u ^ (-1 : ℝ) := by
      refine (norm_mellin_smooth1_le diffν νpos suppν mass_one εpos ε_lt_one.le
        (by rw [hsre]; exact hσ₀) (by rw [hsre]; linarith)).trans ?_
      rw [Real.rpow_neg_one, hPdef, div_le_iff₀ hs0]
      have : 8 / σ₀ * u⁻¹ * ‖s‖ = 4 * (2 * ‖s‖) / (σ₀ * u) := by field_simp; ring
      rw [this, le_div_iff₀ (by positivity)]
      nlinarith
    have hM2 : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ Q * ε ^ (-1 : ℝ) * u ^ (-2 : ℝ) := by
      refine (hM₂ σ₀ hσ₀ s (by rw [hsre]) (by rw [hsre]; linarith) ε εpos ε_lt_one).trans ?_
      have hsq : σ₀ ^ 2 * u ^ 2 ≤ 4 * ‖s‖ ^ 2 := by
        have := mul_self_le_mul_self (by positivity) hlow
        nlinarith
      rw [Real.rpow_neg_one, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu0.le,
        Real.rpow_natCast, hQdef]
      rw [show 4 * C₂ / σ₀ ^ 2 * ε⁻¹ * (u ^ 2)⁻¹ = C₂ * (ε * (σ₀ ^ 2 * u ^ 2 / 4))⁻¹ by
        field_simp]
      gcongr
      linarith
    have hM := le_rpow_mul_rpow (norm_nonneg _) hM1 hM2 hl0 hl1
    rw [interp_rpow_eq hP hQ εpos hu0] at hM
    have hF := hleft t
    have hKt : 0 ≤ K₀ * u ^ θ := by positivity
    have hnormX : ‖(X : ℂ) ^ s‖ = X ^ σ₀ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hsre]
    calc ‖f s‖ = ‖H s / (s - 1)‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ * ‖(X : ℂ) ^ s‖ := by
          show ‖H s / (s - 1) * 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s‖ = _
          rw [norm_mul, norm_mul]
      _ ≤ (K₀ * u ^ θ) * (P ^ (1 - l) * Q ^ l * ε ^ (-l) * u ^ (-1 - l)) * X ^ σ₀ := by
          rw [hnormX]
          gcongr
      _ = K₀ * P ^ (1 - l) * Q ^ l * X ^ σ₀ * ε ^ (-l) * (u ^ θ * u ^ (-1 - l)) := by ring
      _ = _ := by
          rw [← Real.rpow_add hu0, hu, add_comm (|t|) 1, hr]
          congr 2; ring
  have hint : Integrable fun t : ℝ =>
      K₀ * P ^ (1 - l) * Q ^ l * X ^ σ₀ * ε ^ (-l) * (1 + |t|) ^ (-r) :=
    hbase.const_mul _
  have hVI : ‖VerticalIntegral' f σ₀‖ ≤ ‖∫ t : ℝ, f ((σ₀ : ℂ) + (t : ℂ) * I)‖ := by
    simp only [VerticalIntegral', VerticalIntegral, norm_smul, Complex.norm_I, one_mul]
    have h2pi : ‖(1 : ℂ) / (2 * ↑π * I)‖ ≤ 1 := by
      rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
      rw [div_le_one (mul_pos (by norm_num) Real.pi_pos)]
      have : (1 : ℝ) ≤ ‖(2 : ℂ)‖ * π := by
        rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
        nlinarith [Real.pi_gt_three]
      exact this
    calc ‖(1 : ℂ) / (2 * ↑π * I)‖ * ‖∫ t : ℝ, f ((σ₀ : ℂ) + (t : ℂ) * I)‖
        ≤ 1 * ‖∫ t : ℝ, f ((σ₀ : ℂ) + (t : ℂ) * I)‖ := by gcongr
      _ = _ := one_mul _
  refine hVI.trans ((norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)).trans ?_)
  rw [integral_const_mul]
  apply le_of_eq
  rw [← hIr]
  ring

/-! ## The asymptotic -/

/-- **Counting with a holomorphic continuation.**  Under the hypotheses of the module docstring,
`Σ_{n ≤ X} c(n) = H(1) X + O(X^{(θ + σ₀)/(1 + θ) + κ})` for every `κ > 0`. -/
theorem exists_norm_sum_sub_le (c : ℕ → ℂ) (hc0 : c 0 = 0) (hc : ∀ n, ‖c n‖ ≤ 1)
    {H : ℂ → ℂ} {a σ₀ : ℝ} (ha : a < σ₀) (hσ₀ : 0 < σ₀) (hσ₀1 : σ₀ < 1)
    (hH : DifferentiableOn ℂ H {s | a < s.re})
    (hLS : ∀ s : ℂ, 1 < s.re → H s / (s - 1) = LSeries c s)
    {K T₀ κ₁ : ℝ} (hκ₁ : κ₁ < 2)
    (hstrip : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 3 / 2 → T₀ ≤ |s.im| →
      ‖H s / (s - 1)‖ ≤ K * |s.im| ^ κ₁)
    {K₀ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hleft : ∀ t : ℝ, ‖H (σ₀ + t * I) / (σ₀ + t * I - 1)‖ ≤ K₀ * (|t| + 1) ^ θ)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
      ‖∑ n ∈ Finset.Iic ⌊X⌋₊, c n - H 1 * X‖ ≤ C * X ^ ((θ + σ₀) / (1 + θ) + κ) := by
  obtain ⟨ν, hνsmooth, hνnonneg, hνsupp, hνmass⟩ := SmoothExistence
  have diffν : ContDiff ℝ 1 ν := hνsmooth.of_le (by exact_mod_cast le_top)
  have mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  have νpos : ∀ x > 0, 0 ≤ ν x := fun x _ => hνnonneg x
  obtain ⟨C₃, hC₃⟩ := (MellinOfSmooth1c diffν hνsupp mass_one).bound
  obtain ⟨u, hu0, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hC₃
  set κ'' : ℝ := min κ (1 - θ) with hκ''
  have hκ''0 : 0 < κ'' := lt_min hκ (by linarith)
  have hκ''κ : κ'' ≤ κ := min_le_left _ _
  have hκ''1 : κ'' ≤ 1 - θ := min_le_right _ _
  set l : ℝ := θ + κ'' with hl
  obtain ⟨B, hB0, hB⟩ := exists_norm_verticalIntegral'_le diffν νpos hνsupp mass_one hσ₀ hσ₀1
    hleft (l := l) (by linarith) (by linarith) (by linarith)
  set γ : ℝ := (1 - σ₀) / (1 + θ) with hγ
  set e : ℝ := (θ + σ₀) / (1 + θ) with he
  have hθ1 : 0 < 1 + θ := by linarith
  have hγ0 : 0 ≤ γ := div_nonneg (by linarith) hθ1.le
  have hγ1 : γ ≤ 1 := by rw [hγ, div_le_one hθ1]; linarith
  have he0 : 0 ≤ e := div_nonneg (by linarith) hθ1.le
  have hγe : 1 - γ = e := by rw [hγ, he]; field_simp; ring
  have hσγ : σ₀ + γ * l = e + γ * κ'' := by rw [hγ, he, hl]; field_simp; ring
  have hu0' : 0 < u := hu0
  set ε₁ : ℝ := min u 1 / 2 with hε₁
  have hε₁0 : 0 < ε₁ := half_pos (lt_min hu0' one_pos)
  have hε₁u : ε₁ < u := by have := min_le_left u 1; linarith
  have hε₁1 : ε₁ < 1 := by have := min_le_right u 1; linarith
  refine ⟨3 * ε₁ + 2 + B * ε₁ ^ (-l) + ‖H 1‖ * C₃ * ε₁, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  set ε : ℝ := ε₁ * X ^ (-γ) with hε
  have hXγ : X ^ (-γ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)
  have hXγ0 : 0 < X ^ (-γ) := Real.rpow_pos_of_pos hX0 _
  have hε0 : 0 < ε := by positivity
  have hεε₁ : ε ≤ ε₁ := by rw [hε]; nlinarith
  have hε1 : ε < 1 := by linarith
  have hM1 : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1‖ ≤ C₃ * ε := by
    have := hu ⟨hε0, by linarith⟩
    simpa [Real.norm_eq_abs, abs_of_pos hε0] using this
  have hshift := tsum_smooth1_eq_residue_add diffν νpos hνsupp mass_one c hc0 hc ha hσ₀ hσ₀1 hH
    hLS hκ₁ hstrip hθ hleft hX0 hε0 hε1
  have hunsm := norm_sum_sub_tsum_smooth1_le νpos hνsupp mass_one c hc0 hc hX0 hε0 hε1
  have hVI := hB X hX0 ε hε0 hε1
  set M1 := 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1
  have hdec : ∑ n ∈ Finset.Iic ⌊X⌋₊, c n - H 1 * X =
      (∑ n ∈ Finset.Iic ⌊X⌋₊, c n - ∑' n, c n * Smooth1 ν ε (n / X)) +
        VerticalIntegral' (perronIntegrand ν H ε X) σ₀ + H 1 * (M1 - 1) * X := by
    rw [hshift]; ring
  have hεX : ε * X = ε₁ * X ^ e := by
    rw [hε, mul_assoc, ← hγe, Real.rpow_sub hX0, Real.rpow_one, Real.rpow_neg hX0.le]
    field_simp
  have hXl : X ^ σ₀ * ε ^ (-l) ≤ ε₁ ^ (-l) * X ^ (e + κ) := by
    have h1 : X ^ σ₀ * ε ^ (-l) = ε₁ ^ (-l) * X ^ (e + γ * κ'') := by
      rw [hε, Real.mul_rpow hε₁0.le hXγ0.le, ← Real.rpow_mul hX0.le, ← hσγ,
        show σ₀ + γ * l = σ₀ + -γ * -l by ring, Real.rpow_add hX0]
      ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX ?_) (by positivity)
    nlinarith
  have hXe : X ^ e ≤ X ^ (e + κ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hXe1 : 1 ≤ X ^ (e + κ) := Real.one_le_rpow hX (by linarith)
  have hC₃0 : 0 ≤ C₃ := by
    have := (norm_nonneg _).trans hM1
    exact nonneg_of_mul_nonneg_left this hε0
  rw [hdec]
  calc ‖(∑ n ∈ Finset.Iic ⌊X⌋₊, c n - ∑' n, c n * Smooth1 ν ε (n / X)) +
        VerticalIntegral' (perronIntegrand ν H ε X) σ₀ + H 1 * (M1 - 1) * X‖
      ≤ (3 * ε * X + 2) + B * X ^ σ₀ * ε ^ (-l) + ‖H 1‖ * (C₃ * ε) * X := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add hunsm hVI)) ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
        gcongr
    _ = 3 * (ε * X) + 2 + B * (X ^ σ₀ * ε ^ (-l)) + ‖H 1‖ * C₃ * (ε * X) := by ring
    _ ≤ 3 * (ε₁ * X ^ (e + κ)) + 2 * X ^ (e + κ) + B * (ε₁ ^ (-l) * X ^ (e + κ)) +
          ‖H 1‖ * C₃ * (ε₁ * X ^ (e + κ)) := by
        rw [hεX]
        gcongr
        linarith
    _ = (3 * ε₁ + 2 + B * ε₁ ^ (-l) + ‖H 1‖ * C₃ * ε₁) * X ^ (e + κ) := by ring

end GaloisForLFunctions.HTGeometry.SmoothedPerron
