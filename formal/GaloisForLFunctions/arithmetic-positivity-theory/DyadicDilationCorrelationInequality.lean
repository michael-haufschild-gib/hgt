import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialPhaseHarmonicLayers

/-!
# Dyadic dilation inequality for real phase combinations

For a real family `b` on a dyadic scale block `M ≤ n + 1 ≤ 2M` let
`B_b(v) = ∑_n b_n Φ_{n+1}(v)` be its real phase combination. For a weight `φ` integrable on
`(1, ∞)` whose cosine transform `F_φ(f) = ∫_{v>1} φ(v) cos(2πfv) dv` satisfies `|F_φ| ≤ A` and
`|F_φ(f)| ≤ B/f²`, every integer dilation `r ≥ 1` obeys

`|∫_{v>1} φ(v) B_b(v) B_b(rv) dv| ≤ (4/π⁴) K(A, B) r^{-1/2} ∑ b_n²`,

with an absolute constant `K(A, B)`, uniformly in `M`, in the number and positions of the scales,
and in `b`.

The proof expands `B_b` into harmonic layers with weights `|w_k| ≤ 1/k²`. The cross-scale kernel
of harmonics `k` and `l` consists of the values of `F_φ` at the differences and sums of the
frequencies `kθ_n` and `lrθ'_{n'}`, where `θ, θ' ∈ {λ_{n+1}, n + 1}`. Each branch is
`11/12`-spaced, so the Schur test bounds the kernel by `A + O(B/(lr)²)` near the resonance
`k ≈ lr` and by `O(B/(lr)²)` away from it. The resonance is paid by the weights `1/k²`, which
gives the factor `r^{-1/2}`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private theorem sum_filter_gt_inv_sq_le (T : Finset ℕ) (m₀ : ℕ) :
    ∑ m ∈ T.filter (fun m => m₀ < m), 1 / ((m : ℝ) - m₀) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  have hs : Summable fun d : ℕ => 1 / (d : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hinj : Set.InjOn (fun m : ℕ => m - m₀) ↑(T.filter (fun m => m₀ < m)) := by
    intro a ha c hc h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hc
    simp only at h
    omega
  have heq : ∑ m ∈ T.filter (fun m => m₀ < m), 1 / ((m : ℝ) - m₀) ^ 2 =
      ∑ d ∈ (T.filter (fun m => m₀ < m)).image (fun m => m - m₀), 1 / (d : ℝ) ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [Finset.mem_filter] at hm
    rw [Nat.cast_sub hm.2.le]
  rw [heq, ← hasSum_zeta_two.tsum_eq]
  exact hs.sum_le_tsum _ fun d _ => by positivity

private theorem sum_filter_lt_inv_sq_le (T : Finset ℕ) (m₀ : ℕ) :
    ∑ m ∈ T.filter (fun m => m < m₀), 1 / ((m : ℝ) - m₀) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  have hs : Summable fun d : ℕ => 1 / (d : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hinj : Set.InjOn (fun m : ℕ => m₀ - m) ↑(T.filter (fun m => m < m₀)) := by
    intro a ha c hc h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hc
    simp only at h
    omega
  have heq : ∑ m ∈ T.filter (fun m => m < m₀), 1 / ((m : ℝ) - m₀) ^ 2 =
      ∑ d ∈ (T.filter (fun m => m < m₀)).image (fun m => m₀ - m), 1 / (d : ℝ) ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [Finset.mem_filter] at hm
    rw [Nat.cast_sub hm.2.le, ← neg_sub, neg_sq]
  rw [heq, ← hasSum_zeta_two.tsum_eq]
  exact hs.sum_le_tsum _ fun d _ => by positivity

/-- Inverse squared offsets from a fixed index sum to at most `π²/3`. -/
theorem sum_erase_inv_sq_le (T : Finset ℕ) (m₀ : ℕ) :
    ∑ m ∈ T.erase m₀, 1 / ((m : ℝ) - m₀) ^ 2 ≤ Real.pi ^ 2 / 3 := by
  rw [← Finset.filter_ne' T m₀, ← Finset.sum_filter_add_sum_filter_not _ (fun m => m₀ < m)]
  have h1 : (T.filter (fun m => m ≠ m₀)).filter (fun m => m₀ < m) = T.filter (fun m => m₀ < m) := by
    ext m; simp only [Finset.mem_filter]; constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  have h2 : (T.filter (fun m => m ≠ m₀)).filter (fun m => ¬ m₀ < m) = T.filter (fun m => m < m₀) := by
    ext m; simp only [Finset.mem_filter]; constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, by omega⟩
  rw [h1, h2]
  have := sum_filter_gt_inv_sq_le T m₀
  have := sum_filter_lt_inv_sq_le T m₀
  linarith

/-- **Spaced summation.** If `|F| ≤ A` and `|F(f)| ≤ B/f²` off the origin, and the points `y_m`
are `s`-spaced along the indices, then `∑_m |F(x - y_m)| ≤ A + (4B/s²)(π²/3)` for every `x`. -/
theorem sum_abs_le_of_spaced {F : ℝ → ℝ} {A B : ℝ} (hA : ∀ f, |F f| ≤ A)
    (hB : ∀ f, f ≠ 0 → |F f| ≤ B / f ^ 2) (hB0 : 0 ≤ B) (T : Finset ℕ) (y : ℕ → ℝ) (x : ℝ)
    {s : ℝ} (hs : 0 < s) (hsp : ∀ m ∈ T, ∀ m' ∈ T, s * |(m : ℝ) - m'| ≤ |y m - y m'|) :
    ∑ m ∈ T, |F (x - y m)| ≤ A + 4 * B / s ^ 2 * (Real.pi ^ 2 / 3) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp only [Finset.sum_empty]; positivity
  obtain ⟨m₀, hm₀, hmin⟩ := T.exists_min_image (fun m => |x - y m|) hT
  rw [← Finset.add_sum_erase T _ hm₀]
  refine add_le_add (hA _) ?_
  have hterm : ∀ m ∈ T.erase m₀, |F (x - y m)| ≤ 4 * B / s ^ 2 * (1 / ((m : ℝ) - m₀) ^ 2) := by
    intro m hm
    have hm' := Finset.mem_of_mem_erase hm
    have hne : (m : ℝ) ≠ m₀ := by exact_mod_cast Finset.ne_of_mem_erase hm
    have hd : 0 < |(m : ℝ) - m₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hsp' := hsp m hm' m₀ hm₀
    have htri : |y m - y m₀| ≤ 2 * |x - y m| := by
      have := abs_sub_le (y m) x (y m₀)
      rw [abs_sub_comm (y m) x, abs_sub_comm x (y m₀)] at this
      have h2 := hmin m hm'
      rw [abs_sub_comm (y m₀) x] at this
      linarith
    have hlow : s / 2 * |(m : ℝ) - m₀| ≤ |x - y m| := by linarith
    have hpos : 0 < |x - y m| := lt_of_lt_of_le (by positivity) hlow
    have hxne : x - y m ≠ 0 := abs_pos.mp hpos
    refine (hB _ hxne).trans ?_
    rw [← sq_abs (x - y m)]
    have hsq : (s / 2 * |(m : ℝ) - m₀|) ^ 2 ≤ |x - y m| ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    rw [div_le_iff₀ (by positivity)]
    have e : 4 * B / s ^ 2 * (1 / ((m : ℝ) - m₀) ^ 2) * |x - y m| ^ 2 =
        B * (|x - y m| ^ 2 / (s / 2 * |(m : ℝ) - m₀|) ^ 2) := by
      rw [mul_pow]
      field_simp
      rw [sq_abs]
      ring
    rw [e]
    have h1 : 1 ≤ |x - y m| ^ 2 / (s / 2 * |(m : ℝ) - m₀|) ^ 2 := by
      rw [one_le_div (by positivity)]; exact hsq
    nlinarith
  calc ∑ m ∈ T.erase m₀, |F (x - y m)| ≤ ∑ m ∈ T.erase m₀, 4 * B / s ^ 2 * (1 / ((m : ℝ) - m₀) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = 4 * B / s ^ 2 * ∑ m ∈ T.erase m₀, 1 / ((m : ℝ) - m₀) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 * B / s ^ 2 * (Real.pi ^ 2 / 3) :=
        mul_le_mul_of_nonneg_left (sum_erase_inv_sq_le T m₀) (by positivity)

/-- **Far summation.** If every point is at distance at least `D > 0`, then
`∑_m |F(z_m)| ≤ |T| B / D²`. -/
theorem sum_abs_le_of_far {F : ℝ → ℝ} {B : ℝ} (hB : ∀ f, f ≠ 0 → |F f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    (T : Finset ℕ) (z : ℕ → ℝ) {D : ℝ} (hD : 0 < D) (hfar : ∀ m ∈ T, D ≤ |z m|) :
    ∑ m ∈ T, |F (z m)| ≤ T.card * (B / D ^ 2) := by
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul T _ _ fun m hm => ?_
  have hz : z m ≠ 0 := abs_pos.mp (lt_of_lt_of_le hD (hfar m hm))
  refine (hB _ hz).trans ?_
  rw [← sq_abs (z m)]
  exact div_le_div_of_nonneg_left hB0 (by positivity) (pow_le_pow_left₀ hD.le (hfar m hm) 2)


/-- A dyadic scale block: every scale `n + 1` lies in `[M, 2M]`. -/
def DyadicScaleBlock (S : Finset ℕ) (M : ℕ) : Prop :=
  ∀ n ∈ S, M ≤ n + 1 ∧ n + 1 ≤ 2 * M

theorem DyadicScaleBlock.card_le {S : Finset ℕ} {M : ℕ} (h : DyadicScaleBlock S M) :
    S.card ≤ M + 1 := by
  have hsub : S ⊆ Finset.Icc (M - 1) (2 * M - 1) := fun n hn => by
    have := h n hn; simp only [Finset.mem_Icc]; omega
  calc S.card ≤ (Finset.Icc (M - 1) (2 * M - 1)).card := Finset.card_le_card hsub
    _ ≤ M + 1 := by simp only [Nat.card_Icc]; omega

/-- The two frequency branches of the scale `n + 1`: the shifted frequency `λ_{n+1}` and the
integer `n + 1`. -/
def scaleBranch (shifted : Bool) (n : ℕ) : ℝ :=
  if shifted then factorialShiftedFreq (n + 1) else ((n + 1 : ℕ) : ℝ)

theorem scaleBranch_bounds (shifted : Bool) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ≤ scaleBranch shifted n ∧ scaleBranch shifted n ≤ ((n + 1 : ℕ) : ℝ) + 1 / 12 := by
  unfold scaleBranch
  cases shifted
  · simp
  · have := factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)
    simp only [if_true]
    constructor <;> linarith [this.1, this.2]

/-- Both branches are `11/12`-spaced along the scales. -/
theorem scaleBranch_spacing (shifted : Bool) (m m' : ℕ) :
    (11 / 12 : ℝ) * |(m : ℝ) - m'| ≤ |scaleBranch shifted m - scaleBranch shifted m'| := by
  rcases eq_or_ne m m' with rfl | hne
  · simp
  have hd : (1 : ℝ) ≤ |(m : ℝ) - m'| := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_sub_comm, abs_of_pos (by exact_mod_cast (sub_pos.mpr (by exact_mod_cast h : (m:ℝ) < m')))]
      have : (m : ℝ) + 1 ≤ m' := by exact_mod_cast h
      linarith
    · rw [abs_of_pos (by exact_mod_cast (sub_pos.mpr (by exact_mod_cast h : (m':ℝ) < m)))]
      have : (m' : ℝ) + 1 ≤ m := by exact_mod_cast h
      linarith
  have hm := scaleBranch_bounds shifted m
  have hm' := scaleBranch_bounds shifted m'
  push_cast at hm hm'
  have key : |(m : ℝ) - m'| - 1 / 12 ≤ |scaleBranch shifted m - scaleBranch shifted m'| := by
    rcases le_total (m : ℝ) m' with h | h
    · rw [abs_of_nonpos (by linarith), abs_sub_comm]
      calc -((m : ℝ) - m') - 1 / 12 ≤ scaleBranch shifted m' - scaleBranch shifted m := by linarith
        _ ≤ |scaleBranch shifted m' - scaleBranch shifted m| := le_abs_self _
    · rw [abs_of_nonneg (by linarith)]
      calc (m : ℝ) - m' - 1 / 12 ≤ scaleBranch shifted m - scaleBranch shifted m' := by linarith
        _ ≤ |scaleBranch shifted m - scaleBranch shifted m'| := le_abs_self _
  linarith

/-- On a dyadic block every branch frequency lies in `[M, 3M]`. -/
theorem scaleBranch_mem_block {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (h : DyadicScaleBlock S M)
    (shifted : Bool) {n : ℕ} (hn : n ∈ S) :
    (M : ℝ) ≤ scaleBranch shifted n ∧ scaleBranch shifted n ≤ 3 * M := by
  have hb := scaleBranch_bounds shifted n
  have h1 : (M : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (h n hn).1
  have h2 : ((n + 1 : ℕ) : ℝ) ≤ 2 * M := by exact_mod_cast (h n hn).2
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  constructor <;> linarith [hb.1, hb.2]


/-- Resonance bound on a dyadic block: near the resonance `q/4 < p < 4q` the nearest term costs
`A` and the spaced remainder `O(B/q²)`; away from it every term costs `O(B/q²)`. -/
def dyadicResonanceBound (A B p q : ℝ) : ℝ :=
  if q < 4 * p ∧ p < 4 * q then A + 80 * B / q ^ 2 * (Real.pi ^ 2 / 3) else 32 * B / q ^ 2

private theorem card_mul_le_of_block {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (h : DyadicScaleBlock S M)
    {B q : ℝ} (hB0 : 0 ≤ B) (hq : 0 < q) :
    (S.card : ℝ) * (B / (q * M / 4) ^ 2) ≤ 32 * B / q ^ 2 := by
  have hc : (S.card : ℝ) ≤ M + 1 := by exact_mod_cast h.card_le
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  rw [div_pow, mul_pow, div_div_eq_mul_div]
  calc (S.card : ℝ) * (B * 4 ^ 2 / (q ^ 2 * (M : ℝ) ^ 2)) ≤ (M + 1) * (B * 4 ^ 2 / (q ^ 2 * (M : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 16 * B / q ^ 2 * ((M + 1) / (M : ℝ) ^ 2) := by field_simp; ring
    _ ≤ 16 * B / q ^ 2 * 2 := by
        gcongr
        rw [div_le_iff₀ (by positivity)]; nlinarith
    _ = 32 * B / q ^ 2 := by ring

private theorem card_mul_le_of_block' {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (h : DyadicScaleBlock S M)
    {B q : ℝ} (hB0 : 0 ≤ B) (hq : 0 < q) :
    (S.card : ℝ) * (B / (q * M) ^ 2) ≤ 2 * B / q ^ 2 := by
  have hc : (S.card : ℝ) ≤ M + 1 := by exact_mod_cast h.card_le
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  rw [mul_pow]
  calc (S.card : ℝ) * (B / (q ^ 2 * (M : ℝ) ^ 2)) ≤ (M + 1) * (B / (q ^ 2 * (M : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = B / q ^ 2 * ((M + 1) / (M : ℝ) ^ 2) := by field_simp
    _ ≤ B / q ^ 2 * 2 := by
        gcongr
        rw [div_le_iff₀ (by positivity)]; nlinarith
    _ = 2 * B / q ^ 2 := by ring

section CosineTransform

variable {F : ℝ → ℝ} {A B : ℝ} (hA : ∀ f, |F f| ≤ A) (hB : ∀ f, f ≠ 0 → |F f| ≤ B / f ^ 2)
  (hB0 : 0 ≤ B)
include hA hB hB0

/-- **Row difference sum on a dyadic block.** -/
theorem sum_abs_sub_branch_le {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hS : DyadicScaleBlock S M)
    {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) {x : ℝ} (hx : p * M ≤ x ∧ x ≤ p * (3 * M)) (j : Bool) :
    ∑ n ∈ S, |F (x - q * scaleBranch j n)| ≤ dyadicResonanceBound A B p q := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  unfold dyadicResonanceBound
  split_ifs with hnear
  · have hq0 : 0 < q := by linarith
    have h := sum_abs_le_of_spaced hA hB hB0 S (fun n => q * scaleBranch j n) x
      (s := 11 / 12 * q) (by positivity) fun m _ m' _ => by
        rw [← mul_sub, abs_mul, abs_of_pos hq0]
        calc 11 / 12 * q * |(m : ℝ) - m'| = q * (11 / 12 * |(m : ℝ) - m'|) := by ring
          _ ≤ q * |scaleBranch j m - scaleBranch j m'| :=
              mul_le_mul_of_nonneg_left (scaleBranch_spacing j m m') hq0.le
    have hc : 4 * B / (11 / 12 * q) ^ 2 ≤ 80 * B / q ^ 2 := by
      rw [mul_pow, ← div_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 3)
    linarith
  · have hD : 0 < q * M / 4 := by positivity
    have hfar : ∀ n ∈ S, q * M / 4 ≤ |x - q * scaleBranch j n| := by
      intro n hn
      have hb := scaleBranch_mem_block hM hS j hn
      rcases not_and_or.mp hnear with h1 | h1 <;> push Not at h1
      · rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]; nlinarith
      · rw [abs_of_nonneg (by nlinarith)]; nlinarith
    exact (sum_abs_le_of_far hB hB0 S _ hD hfar).trans (card_mul_le_of_block hM hS hB0 (by linarith))

/-- **Column difference sum on a dyadic block.** -/
theorem sum_abs_branch_sub_le {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hS : DyadicScaleBlock S M)
    {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) {x : ℝ} (hx : q * M ≤ x ∧ x ≤ q * (3 * M)) (i : Bool) :
    ∑ n ∈ S, |F (p * scaleBranch i n - x)| ≤ dyadicResonanceBound A B p q := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hA' : ∀ f, |(fun f => F (-f)) f| ≤ A := fun f => hA _
  have hB' : ∀ f, f ≠ 0 → |(fun f => F (-f)) f| ≤ B / f ^ 2 := fun f hf => by
    have := hB (-f) (neg_ne_zero.mpr hf); rwa [neg_sq] at this
  unfold dyadicResonanceBound
  split_ifs with hnear
  · have hq0 : 0 < q := by linarith
    have hp0 : 0 < p := by linarith
    have h := sum_abs_le_of_spaced hA' hB' hB0 S (fun n => p * scaleBranch i n) x
      (s := 11 / 12 * p) (by positivity) fun m _ m' _ => by
        rw [← mul_sub, abs_mul, abs_of_pos hp0]
        calc 11 / 12 * p * |(m : ℝ) - m'| = p * (11 / 12 * |(m : ℝ) - m'|) := by ring
          _ ≤ p * |scaleBranch i m - scaleBranch i m'| :=
              mul_le_mul_of_nonneg_left (scaleBranch_spacing i m m') hp0.le
    simp only [neg_sub] at h
    have hpq : 1 / p ^ 2 ≤ 16 / q ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hnear.1]
    have hc : 4 * B / (11 / 12 * p) ^ 2 ≤ 80 * B / q ^ 2 := by
      calc 4 * B / (11 / 12 * p) ^ 2 = 4 * B / (11 / 12 : ℝ) ^ 2 * (1 / p ^ 2) := by
            rw [mul_pow]; field_simp
        _ ≤ 4 * B / (11 / 12 : ℝ) ^ 2 * (16 / q ^ 2) := by gcongr
        _ = (9216 / 121) * B / q ^ 2 := by ring
        _ ≤ 80 * B / q ^ 2 := by gcongr; norm_num
    have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 3)
    linarith
  · have hD : 0 < q * M / 4 := by positivity
    have hfar : ∀ n ∈ S, q * M / 4 ≤ |p * scaleBranch i n - x| := by
      intro n hn
      have hb := scaleBranch_mem_block hM hS i hn
      rcases not_and_or.mp hnear with h1 | h1 <;> push Not at h1
      · rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]; nlinarith
      · rw [abs_of_nonneg (by nlinarith)]; nlinarith
    exact (sum_abs_le_of_far hB hB0 S _ hD hfar).trans (card_mul_le_of_block hM hS hB0 (by linarith))

omit hA in
/-- **Sum-frequency terms on a dyadic block.** -/
theorem sum_abs_add_branch_le {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hS : DyadicScaleBlock S M)
    {q : ℝ} (hq : 1 ≤ q) {x : ℝ} (hx : 0 ≤ x) (j : Bool) :
    ∑ n ∈ S, |F (x + q * scaleBranch j n)| ≤ 2 * B / q ^ 2 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hD : 0 < q * M := by positivity
  have hfar : ∀ n ∈ S, q * M ≤ |x + q * scaleBranch j n| := by
    intro n hn
    have hb := scaleBranch_mem_block hM hS j hn
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  exact (sum_abs_le_of_far hB hB0 S _ hD hfar).trans (card_mul_le_of_block' hM hS hB0 (by linarith))

omit hA in
/-- Terms at distance at least `qM` from the origin cost at most `2B/q²` in total. -/
theorem sum_abs_le_of_ge_block {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hS : DyadicScaleBlock S M)
    {q : ℝ} (hq : 1 ≤ q) (z : ℕ → ℝ) (hz : ∀ n ∈ S, q * M ≤ |z n|) :
    ∑ n ∈ S, |F (z n)| ≤ 2 * B / q ^ 2 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  exact (sum_abs_le_of_far hB hB0 S z (by positivity) hz).trans
    (card_mul_le_of_block' hM hS hB0 (by linarith))

end CosineTransform

/-- Sign of the frequency branch in a phase profile `cos(λ) - cos(integer)`. -/
def scaleBranchSign (shifted : Bool) : ℝ := if shifted then 1 else -1

/-- **Cross-scale dilation kernel** of a cosine transform `F` at harmonic frequencies `p` and `q`:
`∑_{i,j} ±(F(pθ_i - qθ'_j) + F(pθ_i + qθ'_j))/2` over the shifted/integer branches. -/
def dyadicCrossKernel (F : ℝ → ℝ) (p q : ℝ) (n n' : ℕ) : ℝ :=
  ∑ i : Bool, ∑ j : Bool, scaleBranchSign i * scaleBranchSign j *
    ((F (p * scaleBranch i n - q * scaleBranch j n') + F (p * scaleBranch i n + q * scaleBranch j n')) / 2)

private theorem abs_dyadicCrossKernel_le (F : ℝ → ℝ) (p q : ℝ) (n n' : ℕ) :
    |dyadicCrossKernel F p q n n'| ≤ ∑ i : Bool, ∑ j : Bool,
      (|F (p * scaleBranch i n - q * scaleBranch j n')| + |F (p * scaleBranch i n + q * scaleBranch j n')|) / 2 := by
  unfold dyadicCrossKernel
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hs : |scaleBranchSign i * scaleBranchSign j| = 1 := by
    unfold scaleBranchSign; cases i <;> cases j <;> norm_num
  rw [abs_mul, hs, one_mul, abs_div, abs_two]
  exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)

/-- **Schur test.** A bilinear form whose kernel has row and column absolute sums at most `R`
is bounded by `R ∑ b²`. -/
theorem abs_bilinear_le_of_row_col (T : Finset ℕ) (b : ℕ → ℝ) (K : ℕ → ℕ → ℝ) {R : ℝ}
    (hrow : ∀ i ∈ T, ∑ j ∈ T, |K i j| ≤ R) (hcol : ∀ j ∈ T, ∑ i ∈ T, |K i j| ≤ R) :
    |∑ i ∈ T, ∑ j ∈ T, b i * b j * K i j| ≤ R * ∑ i ∈ T, b i ^ 2 := by
  have hpt (i j : ℕ) : |b i * b j * K i j| ≤ (b i ^ 2 / 2) * |K i j| + (b j ^ 2 / 2) * |K i j| := by
    rw [abs_mul, abs_mul]
    have := two_mul_le_add_sq |b i| |b j|
    rw [sq_abs, sq_abs] at this
    nlinarith [abs_nonneg (K i j), abs_nonneg (b i), abs_nonneg (b j)]
  calc |∑ i ∈ T, ∑ j ∈ T, b i * b j * K i j| ≤ ∑ i ∈ T, ∑ j ∈ T, |b i * b j * K i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ T, ∑ j ∈ T, ((b i ^ 2 / 2) * |K i j| + (b j ^ 2 / 2) * |K i j|) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    _ = ∑ i ∈ T, (b i ^ 2 / 2) * ∑ j ∈ T, |K i j| + ∑ j ∈ T, (b j ^ 2 / 2) * ∑ i ∈ T, |K i j| := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_comm
    _ ≤ ∑ i ∈ T, (b i ^ 2 / 2) * R + ∑ j ∈ T, (b j ^ 2 / 2) * R :=
        add_le_add (Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hrow i hi) (by positivity))
          (Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hcol j hj) (by positivity))
    _ = R * ∑ i ∈ T, b i ^ 2 := by rw [← Finset.sum_add_distrib, Finset.mul_sum]; congr 1; funext i; ring

/-- **Per-harmonic dyadic dilation bound.** For harmonic frequencies `p, q ≥ 1` on a dyadic block,
the cross-scale kernel defines a bilinear form bounded by `2(ν(p,q) + 2B/q²) ∑ b²`. -/
theorem abs_bilinear_dyadicCrossKernel_le {F : ℝ → ℝ} {A B : ℝ} (hA : ∀ f, |F f| ≤ A)
    (hB : ∀ f, f ≠ 0 → |F f| ≤ B / f ^ 2) (hB0 : 0 ≤ B) {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M)
    (hS : DyadicScaleBlock S M) {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (b : ℕ → ℝ) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel F p q n n'| ≤
      2 * (dyadicResonanceBound A B p q + 2 * B / q ^ 2) * ∑ n ∈ S, b n ^ 2 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  set R := 2 * (dyadicResonanceBound A B p q + 2 * B / q ^ 2)
  refine abs_bilinear_le_of_row_col S b _ (fun n hn => ?_) (fun n' hn' => ?_)
  · calc ∑ n' ∈ S, |dyadicCrossKernel F p q n n'| ≤ ∑ n' ∈ S, ∑ i : Bool, ∑ j : Bool,
          (|F (p * scaleBranch i n - q * scaleBranch j n')| +
            |F (p * scaleBranch i n + q * scaleBranch j n')|) / 2 :=
          Finset.sum_le_sum fun n' _ => abs_dyadicCrossKernel_le F p q n n'
      _ = ∑ i : Bool, ∑ j : Bool, (∑ n' ∈ S, |F (p * scaleBranch i n - q * scaleBranch j n')| +
            ∑ n' ∈ S, |F (p * scaleBranch i n + q * scaleBranch j n')|) / 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ ∑ i : Bool, ∑ j : Bool, (dyadicResonanceBound A B p q + 2 * B / q ^ 2) / 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have hx := scaleBranch_mem_block hM hS i hn
          refine div_le_div_of_nonneg_right (add_le_add ?_ ?_) (by norm_num)
          · exact sum_abs_sub_branch_le hA hB hB0 hM hS hp hq
              ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩ j
          · exact sum_abs_add_branch_le hB hB0 hM hS hq (by nlinarith [hx.1]) j
      _ = R := by simp [R]; ring
  · calc ∑ n ∈ S, |dyadicCrossKernel F p q n n'| ≤ ∑ n ∈ S, ∑ i : Bool, ∑ j : Bool,
          (|F (p * scaleBranch i n - q * scaleBranch j n')| +
            |F (p * scaleBranch i n + q * scaleBranch j n')|) / 2 :=
          Finset.sum_le_sum fun n _ => abs_dyadicCrossKernel_le F p q n n'
      _ = ∑ i : Bool, ∑ j : Bool, (∑ n ∈ S, |F (p * scaleBranch i n - q * scaleBranch j n')| +
            ∑ n ∈ S, |F (p * scaleBranch i n + q * scaleBranch j n')|) / 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ ∑ i : Bool, ∑ j : Bool, (dyadicResonanceBound A B p q + 2 * B / q ^ 2) / 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have hx := scaleBranch_mem_block hM hS j hn'
          refine div_le_div_of_nonneg_right (add_le_add ?_ ?_) (by norm_num)
          · exact sum_abs_branch_sub_le hA hB hB0 hM hS hp hq
              ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩ i
          · refine sum_abs_le_of_ge_block hB hB0 hM hS hq _ fun n hn => ?_
            have hy := scaleBranch_mem_block hM hS i hn
            rw [abs_of_nonneg (by nlinarith [hy.1, hx.1])]
            nlinarith [hy.1, hx.1]
      _ = R := by simp [R]; ring


/-- Real harmonic layer `h_k(v) = ∑_n b_n (cos(2πk λ_{n+1} v) - cos(2πk (n+1) v))`. -/
def realHarmonicLayer (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) (v : ℝ) : ℝ :=
  ∑ n ∈ S, b n * (Real.cos (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v)) -
    Real.cos (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v)))

/-- Real phase combination `∑_n b_n Φ_{n+1}(v)`. -/
def realPhaseCombination (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ n ∈ S, b n * factorialPhaseProfile (n + 1) v

theorem realPhaseCombination_hasSum (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    HasSum (fun k => dyadicHarmonicWeight k * realHarmonicLayer S b k v)
      (-(Real.pi ^ 2 / 2) * realPhaseCombination S b v) := by
  have h := hasSum_sum (s := S) fun n _ => (factorialPhaseProfile_hasSum (n + 1) v).mul_left (b n)
  refine hasSum_of_eq_of_eq h (fun k => ?_) ?_
  · unfold realHarmonicLayer dyadicHarmonicWeight
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  · unfold realPhaseCombination
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring

theorem abs_realHarmonicLayer_le (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) (v : ℝ) :
    |realHarmonicLayer S b k v| ≤ 2 * ∑ n ∈ S, |b n| := by
  unfold realHarmonicLayer
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [abs_mul]
  have h1 := Real.abs_cos_le_one (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v))
  have h2 := Real.abs_cos_le_one (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v))
  have := abs_sub (Real.cos (2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v)))
    (Real.cos (2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v)))
  nlinarith [abs_nonneg (b n)]

/-- Cosine transform `F_φ(f) = ∫_{v>1} φ(v) cos(2πfv) dv` of a weight. -/
def weightCosineTransform (φ : ℝ → ℝ) (f : ℝ) : ℝ :=
  ∫ v in Ioi 1, φ v * Real.cos (2 * Real.pi * f * v)

private theorem integrableOn_mul_bdd {φ g : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1)) (hg : Continuous g)
    {C : ℝ} (hC : ∀ v, |g v| ≤ C) :
    IntegrableOn (fun v => φ v * g v) (Ioi 1) := by
  refine (hφ.norm.const_mul C).mono' (hφ.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC v) (abs_nonneg _)

/-- Product-to-sum for the cosine transform. -/
theorem integral_mul_cos_mul_cos {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1)) (a a' : ℝ) :
    ∫ v in Ioi 1, φ v * (Real.cos (2 * Real.pi * a * v) * Real.cos (2 * Real.pi * a' * v)) =
      (weightCosineTransform φ (a - a') + weightCosineTransform φ (a + a')) / 2 := by
  unfold weightCosineTransform
  have h1 := integrableOn_mul_bdd hφ (by fun_prop : Continuous fun v => Real.cos (2 * Real.pi * (a - a') * v))
    (C := 1) fun v => Real.abs_cos_le_one _
  have h2 := integrableOn_mul_bdd hφ (by fun_prop : Continuous fun v => Real.cos (2 * Real.pi * (a + a') * v))
    (C := 1) fun v => Real.abs_cos_le_one _
  rw [← integral_add h1 h2, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [show 2 * Real.pi * (a - a') * v = 2 * Real.pi * a * v - 2 * Real.pi * a' * v by ring,
    show 2 * Real.pi * (a + a') * v = 2 * Real.pi * a * v + 2 * Real.pi * a' * v by ring,
    Real.cos_sub, Real.cos_add]
  ring

private theorem cos_sub_cos_eq_branch (c : ℝ) (n : ℕ) (v : ℝ) :
    Real.cos (2 * Real.pi * c * (factorialShiftedFreq (n + 1) * v)) -
      Real.cos (2 * Real.pi * c * (((n + 1 : ℕ) : ℝ) * v)) =
      ∑ i : Bool, scaleBranchSign i * Real.cos (2 * Real.pi * (c * scaleBranch i n) * v) := by
  simp only [Fintype.sum_bool, scaleBranchSign, scaleBranch, if_true, Bool.false_eq_true, if_false]
  ring_nf

/-- **Harmonic kernel identity.** The weighted correlation of two harmonic layers, the second
dilated by `r`, is the bilinear form of the cross-scale kernel at frequencies `k` and `l r`. -/
theorem integral_mul_realHarmonicLayer_mul_dilate {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1))
    (S : Finset ℕ) (b : ℕ → ℝ) (k l r : ℕ) :
    ∫ v in Ioi 1, φ v * (realHarmonicLayer S b k v * realHarmonicLayer S b l (r * v)) =
      ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform φ) k ((l * r : ℕ) : ℝ) n n' := by
  have hlayer (c : ℝ) (w : ℝ) (j : ℕ) : realHarmonicLayer S b j w =
      ∑ n ∈ S, b n * ∑ i : Bool, scaleBranchSign i * Real.cos (2 * Real.pi * ((j : ℝ) * scaleBranch i n) * w) := by
    unfold realHarmonicLayer
    exact Finset.sum_congr rfl fun n _ => by rw [cos_sub_cos_eq_branch]
  have hdil (n' : ℕ) (j : Bool) (v : ℝ) :
      Real.cos (2 * Real.pi * ((l : ℝ) * scaleBranch j n') * (r * v)) =
        Real.cos (2 * Real.pi * (((l * r : ℕ) : ℝ) * scaleBranch j n') * v) := by
    congr 1; push_cast; ring
  have hexp : ∀ v, φ v * (realHarmonicLayer S b k v * realHarmonicLayer S b l (r * v)) =
      ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * ∑ i : Bool, ∑ j : Bool, scaleBranchSign i * scaleBranchSign j *
        (φ v * (Real.cos (2 * Real.pi * ((k : ℝ) * scaleBranch i n) * v) *
          Real.cos (2 * Real.pi * (((l * r : ℕ) : ℝ) * scaleBranch j n') * v))) := by
    intro v
    rw [hlayer 0 v k, hlayer 0 (r * v) l, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n' _ => ?_
    simp_rw [hdil, Fintype.sum_bool]
    ring
  have hint (i j : Bool) (n n' : ℕ) : IntegrableOn (fun v => φ v *
      (Real.cos (2 * Real.pi * ((k : ℝ) * scaleBranch i n) * v) *
        Real.cos (2 * Real.pi * (((l * r : ℕ) : ℝ) * scaleBranch j n') * v))) (Ioi 1) :=
    integrableOn_mul_bdd hφ (by fun_prop) (C := 1) fun v => by
      rw [abs_mul]; exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _)
  simp_rw [hexp]
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun n' _ =>
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint i j n n').const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun n' _ => (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint i j n n').const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hint i j n n').const_mul _]
  congr 1
  unfold dyadicCrossKernel
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hint i j n n').const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_cos_mul_cos hφ]


private theorem summable_inv_mul_sqrt : Summable fun k : ℕ => 1 / ((k : ℝ) * Real.sqrt k) := by
  refine (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).congr fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [one_div, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hk0.le (by norm_num)]
    norm_num

/-- Majorant constant of the dyadic dilation inequality. -/
def dyadicDilationConstant (A B : ℝ) : ℝ :=
  4 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B) *
      ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) +
    68 * B * ((∑' k : ℕ, 1 / (k : ℝ) ^ 2) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2)

private theorem weight_mul_resonance_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {k l r : ℕ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) (hr : 1 ≤ r) :
    1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2) *
        (2 * (dyadicResonanceBound A B k ((l * r : ℕ) : ℝ) + 2 * B / ((l * r : ℕ) : ℝ) ^ 2)) ≤
      1 / Real.sqrt r * (4 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B) *
        (1 / ((k : ℝ) * Real.sqrt k) * (1 / (l : ℝ) ^ 2)) + 68 * B * (1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2))) := by
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl0 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hr0 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set q : ℝ := ((l * r : ℕ) : ℝ)
  have hq : q = l * r := by simp [q]
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr (by linarith)
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by linarith)
  have hinvq : 1 / q ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hpi : 0 ≤ 80 * (Real.pi ^ 2 / 3) := by positivity
  unfold dyadicResonanceBound
  split_ifs with hnear
  · -- near resonance: one inverse half power of `k` is traded against `√(l r) ≥ √r`
    have hsq : Real.sqrt r ≤ 2 * Real.sqrt k := by
      have h1 : Real.sqrt r ≤ Real.sqrt q := Real.sqrt_le_sqrt (by rw [hq]; nlinarith)
      have h2 : Real.sqrt q ≤ Real.sqrt (4 * k) := Real.sqrt_le_sqrt hnear.1.le
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h2
      linarith
    have hkk : (k : ℝ) ^ 2 = k * Real.sqrt k * Real.sqrt k := by
      rw [mul_assoc, Real.mul_self_sqrt (by linarith)]; ring
    have htrade : 1 / (k : ℝ) ^ 2 ≤ 2 / ((k : ℝ) * Real.sqrt k) * (1 / Real.sqrt r) := by
      rw [hkk, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos (by linarith : (0 : ℝ) < k) hsk]
    have hbr : 2 * (A + 80 * B / q ^ 2 * (Real.pi ^ 2 / 3) + 2 * B / q ^ 2) ≤
        2 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B) := by
      have : 80 * B / q ^ 2 * (Real.pi ^ 2 / 3) + 2 * B / q ^ 2 =
          (80 * (Real.pi ^ 2 / 3) + 2) * B * (1 / q ^ 2) := by ring
      nlinarith [mul_le_mul_of_nonneg_left hinvq (by positivity : 0 ≤ (80 * (Real.pi ^ 2 / 3) + 2) * B)]
    have h0 : 0 ≤ 2 * (A + 80 * B / q ^ 2 * (Real.pi ^ 2 / 3) + 2 * B / q ^ 2) := by positivity
    calc 1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2) * (2 * (A + 80 * B / q ^ 2 * (Real.pi ^ 2 / 3) + 2 * B / q ^ 2))
        ≤ 2 / ((k : ℝ) * Real.sqrt k) * (1 / Real.sqrt r) * (1 / (l : ℝ) ^ 2) *
            (2 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B)) := by
          gcongr
      _ ≤ _ := by
          have : 0 ≤ 68 * B * (1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2)) := by positivity
          rw [show 2 / ((k : ℝ) * Real.sqrt k) * (1 / Real.sqrt r) * (1 / (l : ℝ) ^ 2) *
              (2 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B)) = 1 / Real.sqrt r *
              (4 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B) * (1 / ((k : ℝ) * Real.sqrt k) * (1 / (l : ℝ) ^ 2)))
              by ring]
          gcongr
          linarith
  · -- away from resonance every term carries `1/(lr)² ≤ 1/√r`
    have hqr : 1 / q ^ 2 ≤ 1 / Real.sqrt r := by
      have h1 : Real.sqrt r ≤ r := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      have h2 : (r : ℝ) ≤ q ^ 2 := by rw [hq]; nlinarith
      exact one_div_le_one_div_of_le hsr (h1.trans h2)
    have : 2 * (32 * B / q ^ 2 + 2 * B / q ^ 2) = 68 * B * (1 / q ^ 2) := by ring
    rw [this]
    have h0 : 0 ≤ 4 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B) *
        (1 / ((k : ℝ) * Real.sqrt k) * (1 / (l : ℝ) ^ 2)) := by positivity
    calc 1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2) * (68 * B * (1 / q ^ 2)) ≤
          1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2) * (68 * B * (1 / Real.sqrt r)) := by gcongr
      _ = 1 / Real.sqrt r * (68 * B * (1 / (k : ℝ) ^ 2 * (1 / (l : ℝ) ^ 2))) := by ring
      _ ≤ _ := by gcongr; linarith

/-- **Dyadic dilation inequality.** Let `φ` be integrable on `(1, ∞)` with cosine transform
bounded by `A` and by `B/f²`. For every finite family on a dyadic scale block and every dilation
`r ≥ 1`, `|∫_{v>1} φ(v) B_b(v) B_b(rv) dv| ≤ (4/π⁴) K(A,B)/√r · ∑ b_n²`: resonances `k ≈ lr`
are confined by the block and paid by the harmonic weights, all other cross-scale terms decay
like `1/f²`. -/
theorem abs_integral_weight_realPhaseCombination_dilate_le {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1))
    {A B : ℝ} (hA : ∀ f, |weightCosineTransform φ f| ≤ A)
    (hB : ∀ f, f ≠ 0 → |weightCosineTransform φ f| ≤ B / f ^ 2) (hB0 : 0 ≤ B)
    {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r) :
    |∫ v in Ioi 1, φ v * (realPhaseCombination S b v * realPhaseCombination S b (r * v))| ≤
      4 / Real.pi ^ 4 * (dyadicDilationConstant A B / Real.sqrt r) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  set B1 := ∑ n ∈ S, |b n|
  have hE : 0 ≤ E := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hB1 : 0 ≤ B1 := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hpi4 : 0 < 4 / Real.pi ^ 4 := by positivity
  set w := dyadicHarmonicWeight
  set h := realHarmonicLayer S b
  have hw2 : Summable fun p : ℕ × ℕ => |w p.1| * |w p.2| :=
    summable_abs_dyadicHarmonicWeight.mul_of_nonneg summable_abs_dyadicHarmonicWeight
      (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  have hhc (k : ℕ) : Continuous (h k) := by
    show Continuous (realHarmonicLayer S b k)
    unfold realHarmonicLayer
    fun_prop
  set f : ℕ × ℕ → ℝ → ℝ := fun p v =>
    4 / Real.pi ^ 4 * (w p.1 * w p.2) * (φ v * (h p.1 v * h p.2 (r * v)))
  have hpt (v : ℝ) : φ v * (realPhaseCombination S b v * realPhaseCombination S b (r * v)) =
      ∑' p, f p v := by
    have h1 := realPhaseCombination_hasSum S b v
    have h2 := realPhaseCombination_hasSum S b (r * v)
    have hs : Summable fun p : ℕ × ℕ => (w p.1 * h p.1 v) * (w p.2 * h p.2 (r * v)) := by
      refine Summable.of_norm_bounded (hw2.mul_right ((2 * B1) ^ 2)) fun p => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      have e1 := abs_realHarmonicLayer_le S b p.1 v
      have e2 := abs_realHarmonicLayer_le S b p.2 (r * v)
      have := mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
      calc |w p.1| * |h p.1 v| * (|w p.2| * |h p.2 (r * v)|) =
            |w p.1| * |w p.2| * (|h p.1 v| * |h p.2 (r * v)|) := by ring
        _ ≤ |w p.1| * |w p.2| * ((2 * B1) * (2 * B1)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = |w p.1| * |w p.2| * (2 * B1) ^ 2 := by ring
    have hm := (h1.mul h2 hs).mul_left (4 / Real.pi ^ 4 * φ v)
    have heq : (fun p => f p v) = fun i => 4 / Real.pi ^ 4 * φ v *
        (dyadicHarmonicWeight i.1 * realHarmonicLayer S b i.1 v *
          (dyadicHarmonicWeight i.2 * realHarmonicLayer S b i.2 (r * v))) := by
      funext p
      simp only [f, w, h]
      ring
    rw [heq, hm.tsum_eq]
    field_simp
    ring
  have hint (p : ℕ × ℕ) : Integrable (f p) (volume.restrict (Ioi 1)) := by
    have hc : Continuous fun v => h p.1 v * h p.2 (r * v) :=
      (hhc p.1).mul ((hhc p.2).comp (continuous_const.mul continuous_id))
    have := integrableOn_mul_bdd hφ hc (C := (2 * B1) * (2 * B1)) fun v => by
        rw [abs_mul]
        exact mul_le_mul (abs_realHarmonicLayer_le S b p.1 v) (abs_realHarmonicLayer_le S b p.2 _)
          (abs_nonneg _) (by positivity)
    exact this.const_mul _
  have hnorm (p : ℕ × ℕ) : ∫ v in Ioi 1, ‖f p v‖ ≤
      4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) * ((2 * B1) ^ 2 * ∫ v in Ioi 1, |φ v|) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on (hint p).norm ((hφ.abs.const_mul _).const_mul _) measurableSet_Ioi
      fun v _ => ?_
    simp only [f, Real.norm_eq_abs, abs_mul, abs_of_pos hpi4]
    have e1 := abs_realHarmonicLayer_le S b p.1 v
    have e2 := abs_realHarmonicLayer_le S b p.2 (r * v)
    have := mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
    have hw : 0 ≤ 4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) := by positivity
    calc 4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) * (|φ v| * (|h p.1 v| * |h p.2 (r * v)|)) ≤
          4 / Real.pi ^ 4 * (|w p.1| * |w p.2|) * (|φ v| * ((2 * B1) * (2 * B1))) := by
          gcongr
      _ = _ := by ring
  have hsumm : Summable fun p => ∫ v in Ioi 1, ‖f p v‖ :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg fun _ => norm_nonneg _) hnorm
      ((hw2.mul_left (4 / Real.pi ^ 4)).mul_right ((2 * B1) ^ 2 * ∫ v in Ioi 1, |φ v|))
  have hexch : ∫ v in Ioi 1, φ v * (realPhaseCombination S b v * realPhaseCombination S b (r * v)) =
      ∑' p, ∫ v in Ioi 1, f p v := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun v _ => hpt v]
    exact (integral_tsum_of_summable_integral_norm hint hsumm).symm
  set m : ℕ × ℕ → ℝ := fun p =>
    4 * (A + (80 * (Real.pi ^ 2 / 3) + 2) * B) * (1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / (p.2 : ℝ) ^ 2)) +
      68 * B * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2))
  have hz2 : Summable fun l : ℕ => 1 / (l : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hm : Summable m := by
    refine ((summable_inv_mul_sqrt.mul_of_nonneg hz2 (fun _ => by positivity) (fun _ => by positivity)).mul_left _).add
      ((hz2.mul_of_nonneg hz2 (fun _ => by positivity) (fun _ => by positivity)).mul_left _)
  have hn1 : Summable fun k : ℕ => ‖1 / ((k : ℝ) * Real.sqrt k)‖ :=
    summable_inv_mul_sqrt.abs.congr fun k => (Real.norm_eq_abs _).symm
  have hn2 : Summable fun l : ℕ => ‖1 / (l : ℝ) ^ 2‖ := hz2.abs.congr fun l => (Real.norm_eq_abs _).symm
  have hmsum : ∑' p, m p = dyadicDilationConstant A B := by
    unfold dyadicDilationConstant
    rw [Summable.tsum_add ((summable_inv_mul_sqrt.mul_of_nonneg hz2 (fun _ => by positivity)
        (fun _ => by positivity)).mul_left _)
      ((hz2.mul_of_nonneg hz2 (fun _ => by positivity) (fun _ => by positivity)).mul_left _),
      tsum_mul_left, tsum_mul_left,
      tsum_mul_tsum_of_summable_norm hn1 hn2, tsum_mul_tsum_of_summable_norm hn2 hn2]
  have hbound (p : ℕ × ℕ) : |∫ v in Ioi 1, f p v| ≤ 4 / Real.pi ^ 4 * (1 / Real.sqrt r) * E * m p := by
    have hmp : 0 ≤ m p := by simp only [m]; positivity
    rcases Nat.eq_zero_or_pos p.1 with hk | hk
    · simp only [f, w, hk, dyadicHarmonicWeight_zero, zero_mul, mul_zero, integral_zero, abs_zero]
      positivity
    rcases Nat.eq_zero_or_pos p.2 with hl | hl
    · simp only [f, w, hl, dyadicHarmonicWeight_zero, zero_mul, mul_zero, integral_zero, abs_zero]
      positivity
    have hr' : (1 : ℝ) ≤ ((p.2 * r : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hk1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hk
    simp only [f]
    rw [integral_const_mul, integral_mul_realHarmonicLayer_mul_dilate hφ, abs_mul, abs_mul, abs_of_pos hpi4]
    have hker := abs_bilinear_dyadicCrossKernel_le hA hB hB0 hM hS hk1 hr' b
    have hwk := abs_dyadicHarmonicWeight_le p.1
    have hwl := abs_dyadicHarmonicWeight_le p.2
    have hmaj := weight_mul_resonance_le hA0 hB0 hk hl hr
    have hR0 : 0 ≤ 2 * (dyadicResonanceBound A B p.1 ((p.2 * r : ℕ) : ℝ) +
        2 * B / ((p.2 * r : ℕ) : ℝ) ^ 2) := by
      unfold dyadicResonanceBound; split_ifs <;> positivity
    calc 4 / Real.pi ^ 4 * |w p.1 * w p.2| *
          |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform φ) p.1 ((p.2 * r : ℕ) : ℝ) n n'|
        ≤ 4 / Real.pi ^ 4 * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2)) *
            (2 * (dyadicResonanceBound A B p.1 ((p.2 * r : ℕ) : ℝ) + 2 * B / ((p.2 * r : ℕ) : ℝ) ^ 2) * E) := by
          rw [abs_mul]
          gcongr
      _ = 4 / Real.pi ^ 4 * E * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) *
            (2 * (dyadicResonanceBound A B p.1 ((p.2 * r : ℕ) : ℝ) + 2 * B / ((p.2 * r : ℕ) : ℝ) ^ 2))) := by ring
      _ ≤ 4 / Real.pi ^ 4 * E * (1 / Real.sqrt r * m p) := by gcongr
      _ = _ := by ring
  have hgs : Summable fun p => 4 / Real.pi ^ 4 * (1 / Real.sqrt r) * E * m p := hm.mul_left _
  have habs : Summable fun p => ‖∫ v in Ioi 1, f p v‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => by rw [Real.norm_eq_abs]; exact hbound p) hgs
  rw [hexch, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans ?_
  refine (habs.tsum_le_tsum (fun p => by rw [Real.norm_eq_abs]; exact hbound p) hgs).trans (le_of_eq ?_)
  rw [tsum_mul_left, hmsum]
  ring

end GaloisForLFunctions.ArithmeticPositivityTheory
