import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinOrderedPrimeGap
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.Bertrand

/-!
# The gap-weighted prime Dirichlet series

Let `p_k` be the `k`-th prime and `g_k = p_{k+1} - p_k`.  Call `θ` an admissible gap-moment
exponent if `Σ_{p_k ≤ X} g_k² ≤ C X^{1+θ}` for all `X ≥ 1` (`GapMomentBound θ`).  Admissible
exponents are `≥ 0` (`GapMomentBound.nonneg`); a pointwise bound `g_k ≤ p_k^r` for large `k` makes
`r` admissible (`gapMomentBound_of_eventually_gap_le`), so Bertrand gives `θ = 1` and the
Hoheisel-type prime supply gives `θ = 71/100` (`gapMomentBound_hoheisel`).

**Theorem** (`exists_gapDirichlet_continuation`).  For admissible `θ`,
`D(s) = Σ_k g_k p_k^{-s}` (absolutely convergent on `Re s > 1`) equals `1/(s - 1) + G(s)` there,
with `G` holomorphic on `Re s > θ`.  The continuation `gapDirichletCont` is holomorphic on
`Re s > θ` away from `s = 1`, where it has a simple pole of residue `1` when `θ < 1`
(`tendsto_sub_one_mul_gapDirichletCont`); for `θ < ½` it is `O(1 + |t|)` on `Re s = ½`
(`norm_gapDirichletCont_critical_le`).

Proof: `g_k p_k^{-s} = ∫_{p_k}^{p_{k+1}} x^{-s} dx + r_k(s)`.  The cell integrals are entire (as
difference quotients `dslope`) and telescope to `2^{1-s}/(s - 1)` on `Re s > 1`; the mean value
inequality gives `|r_k(s)| ≤ |s| g_k² p_k^{-σ-1}`, and Abel summation against the moment bound makes
`Σ_k g_k² p_k^{-σ-1}` converge for `σ > θ`, locally uniformly.
-/

open Complex Filter Topology Set
open scoped Real

namespace RHTower.PrimeGapDirichlet

noncomputable section

/-! ### Primes and gaps -/

/-- The `k`-th prime, `p_0 = 2`. -/
abbrev prime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- The gap `p_{k+1} - p_k`. -/
def gap (k : ℕ) : ℕ := prime (k+1)-prime k

theorem prime_strictMono : StrictMono prime := Nat.nth_strictMono Nat.infinite_setOf_prime

theorem prime_prime (k : ℕ) : (prime k).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k

theorem two_le_prime (k : ℕ) : 2≤ prime k := (prime_prime k).two_le

theorem prime_pos_real (k : ℕ) : (0:ℝ)< prime k := by exact_mod_cast (prime_prime k).pos

theorem one_le_prime_real (k : ℕ) : (1:ℝ)≤ prime k := by exact_mod_cast (prime_prime k).one_lt.le

theorem prime_lt_succ (k : ℕ) : prime k< prime (k+1) := prime_strictMono (Nat.lt_succ_self k)

theorem prime_le_succ_real (k : ℕ) : (prime k:ℝ)≤ prime (k+1) := by exact_mod_cast (prime_lt_succ k).le

theorem one_le_gap (k : ℕ) : 1≤ gap k := by unfold gap; have := prime_lt_succ k; omega

theorem prime_succ_cast (k : ℕ) : (prime (k+1) : ℝ)=prime k+gap k := by
  unfold gap
  rw [Nat.cast_sub (prime_lt_succ k).le]
  ring

theorem gap_cast (k : ℕ) : (gap k : ℝ)=(prime (k+1) : ℝ)-prime k := by rw [prime_succ_cast]; ring

theorem le_prime (k : ℕ) : k≤ prime k := prime_strictMono.id_le k

/-- **Bertrand**: `p_{k+1} ≤ 2 p_k`. -/
theorem prime_succ_le_two_mul (k : ℕ) : prime (k+1)≤2*prime k := by
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (prime k) (by
    have := two_le_prime k; omega)
  by_contra hc
  push Not at hc
  exact absurd (Nat.le_nth_of_lt_nth_succ (lt_of_le_of_lt hle hc) hq) (not_le.mpr hlt)

theorem prime_succ_le_two_mul_real (k : ℕ) : (prime (k+1) : ℝ)≤2*prime k := by
  exact_mod_cast prime_succ_le_two_mul k

theorem prime_zero_real : (prime 0 : ℝ)=2 := by simp [prime, Nat.nth_prime_zero_eq_two]

theorem prime_tendsto : Tendsto (fun k => (prime k : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp prime_strictMono.tendsto_atTop

theorem sum_range_gap (n : ℕ) : (∑ k ∈ Finset.range n, (gap k : ℝ))=prime n-2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, prime_succ_cast]; ring

/-! ### Tangent bounds for `x ↦ x^q`, `q ≤ 0` -/

/-- For `q ≤ 0` and `0 < a ≤ b`: `-q (b-a) b^{q-1} ≤ a^q - b^q ≤ -q (b-a) a^{q-1}`. -/
theorem rpow_sub_rpow_bounds {a b q : ℝ} (ha : 0< a) (hab : a≤ b) (hq : q≤0) :
    -q*(b-a)*b^(q-1)≤ a^q-b^q ∧ a^q-b^q≤ -q*(b-a)*a^(q-1) := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  obtain ⟨c, ⟨hac, hcb⟩, hc⟩ : ∃ c ∈ Ioo a b, q*c^(q-1)=(b^q-a^q)/(b-a) :=
    exists_hasDerivAt_eq_slope (fun x : ℝ => x^q) (fun x => q*x^(q-1)) h
      (fun x hx => (Real.continuousAt_rpow_const x q
        (Or.inl (lt_of_lt_of_le ha hx.1).ne')).continuousWithinAt)
      (fun x hx => Real.hasDerivAt_rpow_const (Or.inl (lt_of_lt_of_le ha hx.1.le).ne'))
  have hba : 0< b-a := by linarith
  have hc0 : 0< c := by linarith
  have hcb' : q*c^(q-1)*(b-a)=b^q-a^q := by rw [hc, div_mul_cancel₀ _ hba.ne']
  have h1 : b^(q-1)≤ c^(q-1) := Real.rpow_le_rpow_of_nonpos hc0 hcb.le (by linarith)
  have h2 : c^(q-1)≤ a^(q-1) := Real.rpow_le_rpow_of_nonpos ha hac.le (by linarith)
  have hk : 0≤ -q*(b-a) := mul_nonneg (by linarith) hba.le
  have e1 := mul_le_mul_of_nonneg_left h1 hk
  have e2 := mul_le_mul_of_nonneg_left h2 hk
  constructor
  · linarith [e1, hcb']
  · linarith [e2, hcb']

/-- Bertrand in rpow form: `a^{-τ} ≤ 2^τ b^{-τ}` when `b ≤ 2a`. -/
theorem rpow_neg_le_two_rpow_mul {a b τ : ℝ} (hb : 0< b) (hb2 : b≤2*a) (hτ : 0≤ τ) :
    a^(-τ)≤2^τ*b^(-τ) := by
  have h1 : a^(-τ)≤ (b/2)^(-τ) := Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  rw [Real.div_rpow hb.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ)≤2), div_inv_eq_mul] at h1
  linarith [mul_comm (b^(-τ)) (2^τ)]

/-! ### The first moment `Σ g_k p_k^{-τ}` -/

/-- `Σ_{k< K} g_k p_k^{-τ} ≤ 2/(τ-1)` for `τ > 1` (Bertrand and telescoping). -/
theorem sum_range_gap_mul_rpow_le {τ : ℝ} (hτ : 1< τ) (K : ℕ) :
    (∑ k ∈ Finset.range K, (gap k : ℝ)*(prime k : ℝ)^(-τ))≤2/(τ-1) := by
  have hτ1 : 0< τ-1 := by linarith
  have hc : 0≤2^τ/(τ-1) := div_nonneg (by positivity) hτ1.le
  have hstep : ∀ k, (gap k : ℝ)*(prime k : ℝ)^(-τ)≤
      2^τ/(τ-1)*((prime k : ℝ)^(1-τ)-(prime (k+1) : ℝ)^(1-τ)) := by
    intro k
    have hT := (rpow_sub_rpow_bounds (prime_pos_real k) (prime_le_succ_real k)
      (by linarith : 1-τ≤0)).1
    rw [show 1-τ-1=-τ by ring] at hT
    have hB := rpow_neg_le_two_rpow_mul (prime_pos_real (k+1)) (prime_succ_le_two_mul_real k)
      (by linarith : (0:ℝ)≤ τ)
    have hg0 : (0:ℝ)≤ gap k := Nat.cast_nonneg _
    calc (gap k : ℝ)*(prime k : ℝ)^(-τ)≤ (gap k : ℝ)*(2^τ*(prime (k+1) : ℝ)^(-τ)) :=
          mul_le_mul_of_nonneg_left hB hg0
      _=2^τ/(τ-1)*((τ-1)*(gap k : ℝ)*(prime (k+1) : ℝ)^(-τ)) := by
          rw [div_mul_eq_mul_div, eq_div_iff hτ1.ne']; ring
      _≤2^τ/(τ-1)*((prime k : ℝ)^(1-τ)-(prime (k+1) : ℝ)^(1-τ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          rw [gap_cast]; linarith [hT]
  calc (∑ k ∈ Finset.range K, (gap k : ℝ)*(prime k : ℝ)^(-τ))≤
        ∑ k ∈ Finset.range K, 2^τ/(τ-1)*((prime k : ℝ)^(1-τ)-(prime (k+1) : ℝ)^(1-τ)) :=
          Finset.sum_le_sum fun k _ => hstep k
    _=2^τ/(τ-1)*((prime 0 : ℝ)^(1-τ)-(prime K : ℝ)^(1-τ)) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_range_sub' (fun k => (prime k : ℝ)^(1-τ)) K
    _≤2^τ/(τ-1)*2^(1-τ) := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        have : (0:ℝ)≤ (prime K : ℝ)^(1-τ) := Real.rpow_nonneg (prime_pos_real K).le _
        rw [prime_zero_real]; linarith
    _=2/(τ-1) := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add (by norm_num : (0:ℝ)<2),
          show τ+(1-τ)=1 by ring, Real.rpow_one]

theorem summable_gap_mul_rpow {τ : ℝ} (hτ : 1< τ) :
    Summable (fun k => (gap k : ℝ)*(prime k : ℝ)^(-τ)) :=
  summable_of_sum_range_le
    (fun k => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (prime_pos_real k).le _))
    (sum_range_gap_mul_rpow_le hτ)

/-! ### The moment hypothesis -/

/-- The gap-moment hypothesis `Σ_{p_k ≤ X} g_k² ≤ C X^{1+θ}` for `X ≥ 1`. -/
def GapMomentBound (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ X : ℝ, 1≤ X →
    (∑ k ∈ (Finset.range (⌊X⌋₊+1)).filter (fun k => (prime k : ℝ)≤ X), ((gap k : ℝ))^2)≤
      C*X^(1+θ)

theorem filter_prime_le_eq (K : ℕ) :
    (Finset.range (⌊(prime K : ℝ)⌋₊+1)).filter (fun k => (prime k : ℝ)≤ prime K)=
      Finset.range (K+1) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Nat.floor_natCast, Nat.cast_le]
  constructor
  · rintro ⟨-, hk⟩
    exact Nat.lt_succ_of_le (prime_strictMono.le_iff_le.mp hk)
  · intro hk
    have hkK : k≤ K := Nat.lt_succ_iff.mp hk
    exact ⟨Nat.lt_succ_of_le (le_trans hkK (le_prime K)), prime_strictMono.monotone hkK⟩

/-- The prefix second moment `Σ_{k ≤ K} g_k²`. -/
def gapSqPrefix (K : ℕ) : ℝ := ∑ k ∈ Finset.range (K+1), ((gap k : ℝ))^2

theorem gapSqPrefix_nonneg (K : ℕ) : 0≤ gapSqPrefix K := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The moment hypothesis in index form: `Σ_{k ≤ K} g_k² ≤ C p_K^{1+θ}` with `C ≥ 0`. -/
theorem gapSqPrefix_le {θ : ℝ} (h : GapMomentBound θ) :
    ∃ C : ℝ, 0≤ C ∧ ∀ K : ℕ, gapSqPrefix K≤ C*(prime K : ℝ)^(1+θ) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, le_max_right _ _, fun K => ?_⟩
  have := hC (prime K) (one_le_prime_real K)
  rw [filter_prime_le_eq] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (prime_pos_real K).le _))

/-- Admissible exponents are nonnegative: `Σ_{k ≤ K} g_k² ≥ p_K - 1`. -/
theorem GapMomentBound.nonneg {θ : ℝ} (h : GapMomentBound θ) : 0≤ θ := by
  obtain ⟨C, -, hC⟩ := gapSqPrefix_le h
  by_contra hθ
  push Not at hθ
  have hlow : ∀ K, (prime K : ℝ)-1≤ C*(prime K : ℝ)^(1+θ) := by
    intro K
    refine le_trans ?_ (hC K)
    have h1 : (prime K : ℝ)+1≤ prime (K+1) := by exact_mod_cast prime_lt_succ K
    calc (prime K : ℝ)-1≤ (prime (K+1) : ℝ)-2 := by linarith
      _=∑ k ∈ Finset.range (K+1), (gap k : ℝ) := (sum_range_gap (K+1)).symm
      _≤ gapSqPrefix K := Finset.sum_le_sum fun k _ => by
          have : (1:ℝ)≤ gap k := by exact_mod_cast one_le_gap k
          nlinarith
  have ht : Tendsto (fun K => |C| *(prime K : ℝ)^θ) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by linarith : 0< -θ)).comp prime_tendsto).const_mul |C|
    simpa only [neg_neg, Function.comp_def, mul_zero] using this
  obtain ⟨K, hK⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).exists
  have hpK := prime_pos_real K
  have h2 : (2:ℝ)≤ prime K := by exact_mod_cast two_le_prime K
  have hθp : 0≤ (prime K : ℝ)^θ := Real.rpow_nonneg hpK.le _
  have hsplit : (prime K : ℝ)^(1+θ)=(prime K : ℝ)*(prime K : ℝ)^θ := by
    rw [Real.rpow_add hpK, Real.rpow_one]
  have hle : C*(prime K : ℝ)^(1+θ)≤ |C| *(prime K : ℝ)^θ*prime K := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg hpK.le hθp)]
  nlinarith [hlow K, mul_lt_mul_of_pos_right hK hpK]

/-- The gaps of the primes `≤ X` sum to at most `2X` (telescoping and Bertrand). -/
theorem sum_gap_filter_le {X : ℝ} (hX : 0≤ X) :
    (∑ k ∈ (Finset.range (⌊X⌋₊+1)).filter (fun k => (prime k : ℝ)≤ X), (gap k : ℝ))≤2*X := by
  set S := (Finset.range (⌊X⌋₊+1)).filter (fun k => (prime k : ℝ)≤ X) with hS
  rcases S.eq_empty_or_nonempty with hS0 | hne
  · rw [hS0, Finset.sum_empty]; linarith
  have hKS : (prime (S.max' hne) : ℝ)≤ X := (Finset.mem_filter.mp (S.max'_mem hne)).2
  have hsub : S⊆Finset.range (S.max' hne+1) := fun k hk =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (S.le_max' k hk))
  have hle : (∑ k ∈ S, (gap k : ℝ))≤∑ k ∈ Finset.range (S.max' hne+1), (gap k : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  rw [sum_range_gap] at hle
  linarith [prime_succ_le_two_mul_real (S.max' hne)]

/-- A pointwise bound `g_k ≤ p_k^r` for all large `k` makes `r` an admissible exponent. -/
theorem gapMomentBound_of_eventually_gap_le {r : ℝ} (hr : 0≤ r)
    (h : ∀ᶠ k in atTop, (gap k : ℝ)≤ (prime k : ℝ)^r) : GapMomentBound r := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  have hC₀ : 0≤∑ k ∈ Finset.range N₀, ((gap k : ℝ))^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨(∑ k ∈ Finset.range N₀, ((gap k : ℝ))^2)+2, fun X hX => ?_⟩
  have hX0 : 0< X := by linarith
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun k => k< N₀)]
  have h1 : (∑ k ∈ ((Finset.range (⌊X⌋₊+1)).filter (fun k => (prime k : ℝ)≤ X)).filter
      (fun k => k< N₀), ((gap k : ℝ))^2)≤∑ k ∈ Finset.range N₀, ((gap k : ℝ))^2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => sq_nonneg _)
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
  have h2 : (∑ k ∈ ((Finset.range (⌊X⌋₊+1)).filter (fun k => (prime k : ℝ)≤ X)).filter
      (fun k => ¬ k< N₀), ((gap k : ℝ))^2)≤ X^r*(2*X) := by
    calc _≤∑ k ∈ ((Finset.range (⌊X⌋₊+1)).filter (fun k => (prime k : ℝ)≤ X)).filter
            (fun k => ¬ k< N₀), X^r*(gap k : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          simp only [Finset.mem_filter, not_lt] at hk
          have hg := hN₀ k hk.2
          have hpX : (prime k : ℝ)^r≤ X^r := Real.rpow_le_rpow (prime_pos_real k).le hk.1.2 hr
          have hg0 : (0:ℝ)≤ gap k := Nat.cast_nonneg _
          nlinarith
      _=X^r*∑ k ∈ ((Finset.range (⌊X⌋₊+1)).filter (fun k => (prime k : ℝ)≤ X)).filter
            (fun k => ¬ k< N₀), (gap k : ℝ) := by rw [Finset.mul_sum]
      _≤ X^r*(2*X) := by
          refine mul_le_mul_of_nonneg_left (le_trans ?_ (sum_gap_filter_le hX0.le))
            (Real.rpow_nonneg hX0.le _)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.cast_nonneg _)
  have hXr : X^(1+r)=X*X^r := by rw [Real.rpow_add hX0, Real.rpow_one]
  have h1X : 1≤ X^(1+r) := Real.one_le_rpow hX (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1X hC₀]

/-- **Bertrand** makes `θ = 1` admissible. -/
theorem gapMomentBound_one : GapMomentBound 1 := by
  refine gapMomentBound_of_eventually_gap_le zero_le_one (Eventually.of_forall fun k => ?_)
  rw [Real.rpow_one, gap_cast]
  linarith [prime_succ_le_two_mul_real k]

/-- The Hoheisel-type supply `p_{k+1} - p_k ≤ p_k^{71/100}` (for large `k`) makes `θ = 71/100`
admissible, unconditionally. -/
theorem gapMomentBound_hoheisel : GapMomentBound (71/100) := by
  refine gapMomentBound_of_eventually_gap_le (by norm_num) ?_
  filter_upwards [Sieve.eventually_nthPrimeSubtype_succ_gap_le_routeTHoheiselEveryBase] with k hk
  rw [gap_cast]
  exact hk

/-! ### Abel summation for the second moment -/

theorem sum_range_gap_sq_mul_rpow_eq (τ : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range (K+1), ((gap k : ℝ))^2*(prime k : ℝ)^(-τ)=
      gapSqPrefix K*(prime K : ℝ)^(-τ)+
        ∑ k ∈ Finset.range K, gapSqPrefix k*((prime k : ℝ)^(-τ)-(prime (k+1) : ℝ)^(-τ)) := by
  induction K with
  | zero => simp [gapSqPrefix]
  | succ K ih =>
    rw [Finset.sum_range_succ (fun k => ((gap k : ℝ))^2*(prime k : ℝ)^(-τ)) (K+1), ih,
      Finset.sum_range_succ (fun k => gapSqPrefix k*((prime k : ℝ)^(-τ)-(prime (k+1) : ℝ)^(-τ))) K]
    have : gapSqPrefix (K+1)=gapSqPrefix K+((gap (K+1) : ℝ))^2 := by
      simp only [gapSqPrefix]; rw [Finset.sum_range_succ]
    rw [this]; ring

/-- **Weighted second moment.**  For admissible `θ` and `τ > 1 + θ`, `Σ_k g_k² p_k^{-τ} < ∞`. -/
theorem summable_gap_sq_mul_rpow {θ τ : ℝ} (h : GapMomentBound θ) (hτ : 1+θ< τ) :
    Summable (fun k => ((gap k : ℝ))^2*(prime k : ℝ)^(-τ)) := by
  obtain ⟨C, hC0, hC⟩ := gapSqPrefix_le h
  have hθ := h.nonneg
  have hτ0 : 0< τ := by linarith
  refine summable_of_sum_range_le (c := C+C*τ*(2/(τ-θ-1)))
    (fun k => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (prime_pos_real k).le _)) ?_
  have hB0 : 0≤2/(τ-θ-1) := div_nonneg (by norm_num) (by linarith)
  intro n
  rcases n with _ | K
  · simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  rw [sum_range_gap_sq_mul_rpow_eq]
  have hB : (∑ k ∈ Finset.range K, (gap k : ℝ)*(prime k : ℝ)^(-(τ-θ)))≤2/(τ-θ-1) :=
    sum_range_gap_mul_rpow_le (by linarith) K
  have hbd : gapSqPrefix K*(prime K : ℝ)^(-τ)≤ C := by
    have ha := prime_pos_real K
    calc gapSqPrefix K*(prime K : ℝ)^(-τ)≤ C*(prime K : ℝ)^(1+θ)*(prime K : ℝ)^(-τ) :=
          mul_le_mul_of_nonneg_right (hC K) (Real.rpow_nonneg ha.le _)
      _=C*(prime K : ℝ)^(1+θ+-τ) := by rw [mul_assoc, ← Real.rpow_add ha]
      _≤ C*1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos (one_le_prime_real K) (by linarith)) hC0
      _=C := mul_one C
  have hterm : ∀ k, gapSqPrefix k*((prime k : ℝ)^(-τ)-(prime (k+1) : ℝ)^(-τ))≤
      C*τ*((gap k : ℝ)*(prime k : ℝ)^(-(τ-θ))) := by
    intro k
    have ha := prime_pos_real k
    have hhi := (rpow_sub_rpow_bounds ha (prime_le_succ_real k) (by linarith : -τ≤0)).2
    have hd0 : 0≤ (prime k : ℝ)^(-τ)-(prime (k+1) : ℝ)^(-τ) :=
      sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos ha (prime_le_succ_real k) (by linarith))
    have hexp : (prime k : ℝ)^(1+θ)*(prime k : ℝ)^(-τ-1)=(prime k : ℝ)^(-(τ-θ)) := by
      rw [← Real.rpow_add ha]; congr 1; ring
    calc gapSqPrefix k*((prime k : ℝ)^(-τ)-(prime (k+1) : ℝ)^(-τ))≤
          C*(prime k : ℝ)^(1+θ)*((prime k : ℝ)^(-τ)-(prime (k+1) : ℝ)^(-τ)) :=
          mul_le_mul_of_nonneg_right (hC k) hd0
      _≤ C*(prime k : ℝ)^(1+θ)*(-(-τ)*((prime (k+1) : ℝ)-prime k)*(prime k : ℝ)^(-τ-1)) :=
          mul_le_mul_of_nonneg_left hhi (mul_nonneg hC0 (Real.rpow_nonneg ha.le _))
      _=C*τ*((gap k : ℝ)*((prime k : ℝ)^(1+θ)*(prime k : ℝ)^(-τ-1))) := by rw [gap_cast]; ring
      _=C*τ*((gap k : ℝ)*(prime k : ℝ)^(-(τ-θ))) := by rw [hexp]
  calc _≤ C+∑ k ∈ Finset.range K, C*τ*((gap k : ℝ)*(prime k : ℝ)^(-(τ-θ))) :=
        add_le_add hbd (Finset.sum_le_sum fun k _ => hterm k)
    _=C+C*τ*∑ k ∈ Finset.range K, (gap k : ℝ)*(prime k : ℝ)^(-(τ-θ)) := by rw [Finset.mul_sum]
    _≤ C+C*τ*(2/(τ-θ-1)) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hB (mul_nonneg hC0 hτ0.le))

/-! ### The cells and the remainders -/

/-- The term `g_k p_k^{-s}`. -/
def gapTerm (k : ℕ) (s : ℂ) : ℂ := (gap k : ℂ)*(prime k : ℂ)^(-s)

/-- The cell integral `∫_{p_k}^{p_{k+1}} x^{-s} dx = (p_k^{1-s} - p_{k+1}^{1-s})/(s - 1)`, as an
entire function of `s`. -/
def gapCell (k : ℕ) : ℂ → ℂ :=
  dslope (fun s => (prime k : ℂ)^(1-s)-(prime (k+1) : ℂ)^(1-s)) 1

/-- The remainder `r_k(s) = g_k p_k^{-s} - ∫_{p_k}^{p_{k+1}} x^{-s} dx`. -/
def gapRemainder (k : ℕ) (s : ℂ) : ℂ := gapTerm k s-gapCell k s

/-- The gap-weighted prime Dirichlet series `D(s) = Σ_k g_k p_k^{-s}`. -/
def gapDirichlet (s : ℂ) : ℂ := ∑' k, gapTerm k s

/-- The regular part `Σ_k r_k(s)`. -/
def gapRegular (s : ℂ) : ℂ := ∑' k, gapRemainder k s

/-- The entire function `(2^{1-s} - 1)/(s - 1)`. -/
def gapPolar : ℂ → ℂ := dslope (fun s => (2:ℂ)^(1-s)) 1

/-- The continuation `1/(s - 1) + (2^{1-s} - 1)/(s - 1) + Σ_k r_k(s)` of `D`. -/
def gapDirichletCont (s : ℂ) : ℂ := 1/(s-1)+(gapPolar s+gapRegular s)

theorem natCast_prime_ne_zero (k : ℕ) : (prime k : ℂ)≠0 := by exact_mod_cast (prime_prime k).ne_zero

theorem differentiable_const_cpow_one_sub {a : ℂ} (ha : a≠0) :
    Differentiable ℂ (fun s : ℂ => a^(1-s)) :=
  (differentiable_id.const_sub 1).const_cpow (Or.inl ha)

theorem differentiable_gapCell (k : ℕ) : Differentiable ℂ (gapCell k) := by
  rw [← differentiableOn_univ, gapCell, Complex.differentiableOn_dslope Filter.univ_mem]
  exact ((differentiable_const_cpow_one_sub (natCast_prime_ne_zero k)).sub
    (differentiable_const_cpow_one_sub (natCast_prime_ne_zero (k+1)))).differentiableOn

theorem differentiable_gapTerm (k : ℕ) : Differentiable ℂ (gapTerm k) :=
  (differentiable_const _).mul (differentiable_id.neg.const_cpow (Or.inl (natCast_prime_ne_zero k)))

theorem differentiable_gapRemainder (k : ℕ) : Differentiable ℂ (gapRemainder k) :=
  (differentiable_gapTerm k).sub (differentiable_gapCell k)

theorem differentiable_gapPolar : Differentiable ℂ gapPolar := by
  rw [← differentiableOn_univ, gapPolar, Complex.differentiableOn_dslope Filter.univ_mem]
  exact (differentiable_const_cpow_one_sub two_ne_zero).differentiableOn

theorem gapCell_of_ne {k : ℕ} {s : ℂ} (hs : s≠1) :
    gapCell k s=((prime k : ℂ)^(1-s)-(prime (k+1) : ℂ)^(1-s))/(s-1) := by
  rw [gapCell, dslope_of_ne _ hs, slope_def_field]
  simp

theorem zero_notMem_uIcc_prime (k : ℕ) :
    (0:ℝ)∉Set.uIcc (prime k : ℝ) (prime (k+1) : ℝ) := by
  rw [Set.uIcc_of_le (prime_le_succ_real k)]
  exact fun h => absurd h.1 (not_le.mpr (prime_pos_real k))

theorem gapCell_eq_integral {k : ℕ} {s : ℂ} (hs : s≠1) :
    gapCell k s=∫ x in (prime k : ℝ)..(prime (k+1) : ℝ), (x : ℂ)^(-s) := by
  rw [integral_cpow (Or.inr ⟨fun h => hs (by linear_combination -h), zero_notMem_uIcc_prime k⟩),
    gapCell_of_ne hs]
  have h1 : (1:ℂ)-s≠0 := sub_ne_zero.mpr (Ne.symm hs)
  have h2 : s-1≠0 := sub_ne_zero.mpr hs
  push_cast
  rw [show -s+1=1-s by ring, div_eq_div_iff h2 h1]
  ring

theorem gapRemainder_eq_integral {k : ℕ} {s : ℂ} (hs : s≠1) :
    gapRemainder k s=∫ x in (prime k : ℝ)..(prime (k+1) : ℝ),
      ((((prime k : ℝ) : ℂ))^(-s)-(x : ℂ)^(-s)) := by
  rw [gapRemainder, gapTerm, intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_cpow (Or.inr (zero_notMem_uIcc_prime k))),
    intervalIntegral.integral_const, ← gapCell_eq_integral hs]
  congr 1
  rw [Complex.real_smul, prime_succ_cast k]
  push_cast
  ring

/-- Mean value bound: `‖x^{-s} - a^{-s}‖ ≤ ‖s‖ a^{-σ-1} (x - a)` for `0 < a ≤ x`, `σ ≥ -1`. -/
theorem norm_cpow_sub_cpow_le {a x : ℝ} (ha : 0< a) (hax : a≤ x) {s : ℂ} (hs : -1≤ s.re) :
    ‖(x : ℂ)^(-s)-(a : ℂ)^(-s)‖≤ ‖s‖*a^(-s.re-1)*(x-a) := by
  have hderiv : ∀ y ∈ Set.Icc a x, HasDerivWithinAt (fun y : ℝ => (y : ℂ)^(-s))
      (-s*(y : ℂ)^(-s-1)) (Set.Icc a x) y := by
    intro y hy
    exact ((Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.2
      (lt_of_lt_of_le ha hy.1))).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbound : ∀ y ∈ Set.Ico a x, ‖-s*(y : ℂ)^(-s-1)‖≤ ‖s‖*a^(-s.re-1) := by
    intro y hy
    have hy0 : 0< y := lt_of_lt_of_le ha hy.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : (-s-1).re=-s.re-1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hy.1 (by linarith))
      (norm_nonneg _)
  exact norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound x ⟨hax, le_rfl⟩

theorem norm_gapRemainder_le_of_ne (k : ℕ) {s : ℂ} (hs : -1≤ s.re) (hs1 : s≠1) :
    ‖gapRemainder k s‖≤ ‖s‖*((gap k : ℝ))^2*(prime k : ℝ)^(-s.re-1) := by
  rw [gapRemainder_eq_integral hs1]
  have hconst : ∀ x ∈ Set.uIoc (prime k : ℝ) (prime (k+1) : ℝ),
      ‖(((prime k : ℝ) : ℂ))^(-s)-(x : ℂ)^(-s)‖≤
        ‖s‖*(prime k : ℝ)^(-s.re-1)*((prime (k+1) : ℝ)-prime k) := by
    intro x hx
    rw [Set.uIoc_of_le (prime_le_succ_real k)] at hx
    rw [norm_sub_rev]
    calc _≤ ‖s‖*(prime k : ℝ)^(-s.re-1)*(x-prime k) :=
          norm_cpow_sub_cpow_le (prime_pos_real k) hx.1.le hs
      _≤ ‖s‖*(prime k : ℝ)^(-s.re-1)*((prime (k+1) : ℝ)-prime k) :=
          mul_le_mul_of_nonneg_left (by linarith [hx.2])
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (prime_pos_real k).le _))
  have := intervalIntegral.norm_integral_le_of_norm_le_const hconst
  rw [abs_of_nonneg (by linarith [prime_le_succ_real k])] at this
  refine this.trans (le_of_eq ?_)
  rw [gap_cast]
  ring

/-- **Remainder bound** `|r_k(s)| ≤ |s| g_k² p_k^{-σ-1}` for `σ > -1`. -/
theorem norm_gapRemainder_le (k : ℕ) {s : ℂ} (hs : -1< s.re) :
    ‖gapRemainder k s‖≤ ‖s‖*((gap k : ℝ))^2*(prime k : ℝ)^(-s.re-1) := by
  rcases ne_or_eq s 1 with hs1 | rfl
  · exact norm_gapRemainder_le_of_ne k hs.le hs1
  have hc : Continuous (fun s : ℂ =>
      ‖gapRemainder k s‖-‖s‖*((gap k : ℝ))^2*(prime k : ℝ)^(-s.re-1)) := by
    have h1 : Continuous (fun s : ℂ => (prime k : ℝ)^(-s.re-1)) :=
      continuous_const.rpow (continuous_re.neg.sub continuous_const)
        (fun _ => Or.inl (prime_pos_real k).ne')
    exact (differentiable_gapRemainder k).continuous.norm.sub
      ((continuous_norm.mul continuous_const).mul h1)
  have hev : ∀ᶠ s in 𝓝[≠] (1:ℂ),
      ‖gapRemainder k s‖-‖s‖*((gap k : ℝ))^2*(prime k : ℝ)^(-s.re-1)≤0 := by
    have hopen : ∀ᶠ s in 𝓝 (1:ℂ), -1< s.re :=
      (continuous_re.tendsto 1).eventually (lt_mem_nhds (by norm_num))
    filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with s hs hs1
    exact sub_nonpos.mpr (norm_gapRemainder_le_of_ne k hs.le hs1)
  have := le_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev
  linarith

/-! ### Convergence and the continuation -/

theorem summable_gapTerm {s : ℂ} (hs : 1< s.re) : Summable (fun k => gapTerm k s) := by
  refine Summable.of_norm_bounded (summable_gap_mul_rpow hs) (fun k => le_of_eq ?_)
  rw [gapTerm, norm_mul, Complex.norm_natCast, Complex.norm_natCast_cpow_of_pos (prime_prime k).pos,
    Complex.neg_re]

theorem summable_gapRemainder {θ : ℝ} (h : GapMomentBound θ) {s : ℂ} (hs : θ< s.re) :
    Summable (fun k => gapRemainder k s) := by
  refine Summable.of_norm_bounded
    ((summable_gap_sq_mul_rpow h (τ := s.re+1) (by linarith)).mul_left ‖s‖) (fun k => ?_)
  have := norm_gapRemainder_le k (s := s) (by linarith [h.nonneg])
  rw [show -s.re-1=-(s.re+1) by ring] at this
  linarith [this]

/-- The cells telescope: `Σ_k ∫_{p_k}^{p_{k+1}} x^{-s} dx = 2^{1-s}/(s - 1)` on `Re s > 1`. -/
theorem hasSum_gapCell {s : ℂ} (hs : 1< s.re) :
    HasSum (fun k => gapCell k s) ((2:ℂ)^(1-s)/(s-1)) := by
  have hs1 : s≠1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs
  have hsum : Summable (fun k => gapCell k s) := by
    have := (summable_gapTerm hs).sub (summable_gapRemainder gapMomentBound_one (s := s) hs)
    simpa [gapRemainder] using this
  have hpartial : ∀ K, ∑ k ∈ Finset.range K, gapCell k s=
      ((2:ℂ)^(1-s)-(prime K : ℂ)^(1-s))/(s-1) := by
    intro K
    simp_rw [gapCell_of_ne hs1, ← Finset.sum_div]
    rw [Finset.sum_range_sub' (fun k => (prime k : ℂ)^(1-s))]
    simp [Nat.nth_prime_zero_eq_two]
  have hlim : Tendsto (fun K => (prime K : ℂ)^(1-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn : ∀ K, ‖(prime K : ℂ)^(1-s)‖=(prime K : ℝ)^(-(s.re-1)) := fun K => by
      rw [Complex.norm_natCast_cpow_of_pos (prime_prime K).pos, Complex.sub_re, Complex.one_re]
      congr 1; ring
    simp_rw [hn]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp prime_tendsto
  refine (hsum.hasSum_iff_tendsto_nat).mpr ?_
  simp_rw [hpartial]
  have := (tendsto_const_nhds (x := (2:ℂ)^(1-s))).sub hlim
  rw [sub_zero] at this
  exact this.div_const (s-1)

/-- On `Re s > 1`: `D(s) = 1/(s - 1) + (2^{1-s} - 1)/(s - 1) + Σ_k r_k(s)`. -/
theorem gapDirichlet_eq {s : ℂ} (hs : 1< s.re) :
    gapDirichlet s=1/(s-1)+(gapPolar s+gapRegular s) := by
  have hs1 : s≠1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs
  have hsplit : gapDirichlet s=∑' k, gapCell k s+gapRegular s := by
    rw [gapDirichlet, gapRegular, ← (hasSum_gapCell hs).summable.tsum_add
      (summable_gapRemainder gapMomentBound_one (s := s) hs)]
    congr 1
    funext k
    rw [gapRemainder]
    ring
  rw [hsplit, (hasSum_gapCell hs).tsum_eq, gapPolar, dslope_of_ne _ hs1, slope_def_field,
    sub_self, Complex.cpow_zero]
  ring

theorem gapDirichletCont_eq {s : ℂ} (hs : 1< s.re) : gapDirichletCont s=gapDirichlet s :=
  (gapDirichlet_eq hs).symm

/-- **The regular part is holomorphic on `Re s > θ`** for every admissible `θ`. -/
theorem differentiableOn_gapRegular {θ : ℝ} (h : GapMomentBound θ) :
    DifferentiableOn ℂ gapRegular {s | θ< s.re} := by
  intro s₀ hs₀
  have hs₀' : θ< s₀.re := hs₀
  obtain ⟨σ₀, hσ₁, hσ₂⟩ : ∃ σ₀, θ< σ₀ ∧ σ₀< s₀.re := ⟨(θ+s₀.re)/2, by linarith, by linarith⟩
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0< R ∧ ‖s₀‖< R := ⟨‖s₀‖+1, by positivity, by linarith⟩
  have hθ := h.nonneg
  set U := {s : ℂ | σ₀< s.re}∩Metric.ball 0 R
  have hU : IsOpen U := (continuous_re.isOpen_preimage _ isOpen_Ioi).inter Metric.isOpen_ball
  have hs₀U : s₀∈U := ⟨hσ₂, mem_ball_zero_iff.mpr hR⟩
  have hdiff : DifferentiableOn ℂ gapRegular U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun k => R*(((gap k : ℝ))^2*(prime k : ℝ)^(-(σ₀+1))))
      ((summable_gap_sq_mul_rpow h (by linarith)).mul_left R)
      (fun k => (differentiable_gapRemainder k).differentiableOn) hU ?_
    intro k w hw
    have hwre : σ₀< w.re := hw.1
    have hwR : ‖w‖< R := mem_ball_zero_iff.mp hw.2
    have h1 : (prime k : ℝ)^(-w.re-1)≤ (prime k : ℝ)^(-(σ₀+1)) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_prime_real k) (by linarith)
    have h2 : 0≤ ((gap k : ℝ))^2 := sq_nonneg _
    have h3 : 0≤ (prime k : ℝ)^(-w.re-1) := Real.rpow_nonneg (prime_pos_real k).le _
    calc ‖gapRemainder k w‖≤ ‖w‖*((gap k : ℝ))^2*(prime k : ℝ)^(-w.re-1) :=
          norm_gapRemainder_le k (by linarith)
      _=‖w‖*(((gap k : ℝ))^2*(prime k : ℝ)^(-w.re-1)) := by ring
      _≤ R*(((gap k : ℝ))^2*(prime k : ℝ)^(-(σ₀+1))) :=
          mul_le_mul hwR.le (mul_le_mul_of_nonneg_left h1 h2) (mul_nonneg h2 h3) hR0.le
  exact ((hdiff s₀ hs₀U).differentiableAt (hU.mem_nhds hs₀U)).differentiableWithinAt

/-- **The gap-weighted prime carrier.**  For every admissible gap-moment exponent `θ`,
`D(s) = 1/(s - 1) + G(s)` on `Re s > 1` with `G` holomorphic on `Re s > θ`. -/
theorem exists_gapDirichlet_continuation {θ : ℝ} (h : GapMomentBound θ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | θ< s.re} ∧
      ∀ s : ℂ, 1< s.re → gapDirichlet s=1/(s-1)+G s :=
  ⟨fun s => gapPolar s+gapRegular s,
    differentiable_gapPolar.differentiableOn.add (differentiableOn_gapRegular h),
    fun _ hs => gapDirichlet_eq hs⟩

/-- The continuation is holomorphic on `Re s > θ` away from `s = 1`. -/
theorem differentiableOn_gapDirichletCont {θ : ℝ} (h : GapMomentBound θ) :
    DifferentiableOn ℂ gapDirichletCont ({s | θ< s.re}\{1}) := by
  have h1 : DifferentiableOn ℂ (fun s : ℂ => 1/(s-1)) ({s | θ< s.re}\{1}) := fun s hs =>
    ((differentiableAt_const (1:ℂ)).div ((differentiableAt_id (𝕜 := ℂ) (x := s)).sub_const 1)
      (sub_ne_zero.mpr hs.2)).differentiableWithinAt
  exact h1.add (differentiable_gapPolar.differentiableOn.add
    ((differentiableOn_gapRegular h).mono fun _ hx => hx.1))

/-- **Simple pole of residue `1` at `s = 1`** (for admissible `θ < 1`). -/
theorem tendsto_sub_one_mul_gapDirichletCont {θ : ℝ} (h : GapMomentBound θ) (hθ : θ<1) :
    Tendsto (fun s => (s-1)*gapDirichletCont s) (𝓝[≠] 1) (𝓝 1) := by
  have hG : ContinuousAt (fun s => gapPolar s+gapRegular s) 1 :=
    (differentiable_gapPolar 1).continuousAt.add
      ((differentiableOn_gapRegular h).differentiableAt
        ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simpa using hθ))).continuousAt
  have h1 : Tendsto (fun s : ℂ => (s-1)*(gapPolar s+gapRegular s)) (𝓝 1)
      (𝓝 ((1-1)*(gapPolar 1+gapRegular 1))) :=
    ((continuous_id.sub (continuous_const (y := (1:ℂ)))).continuousAt.mul hG).tendsto
  rw [sub_self, zero_mul] at h1
  have h2 : Tendsto (fun s : ℂ => 1+(s-1)*(gapPolar s+gapRegular s)) (𝓝[≠] 1) (𝓝 1) := by
    simpa using (h1.mono_left nhdsWithin_le_nhds).const_add 1
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [gapDirichletCont, mul_add (s-1) (1/(s-1)), mul_one_div_cancel (sub_ne_zero.mpr hs)]

/-- **Linear growth on the critical line** for admissible `θ < ½`:
`|D(½ + it)| ≤ C (1 + |t|)`. -/
theorem norm_gapDirichletCont_critical_le {θ : ℝ} (h : GapMomentBound θ) (hθ : θ<1/2) :
    ∃ C : ℝ, ∀ t : ℝ, ‖gapDirichletCont (1/2+t*I)‖≤ C*(1+|t|) := by
  have hsum := summable_gap_sq_mul_rpow h (τ := 3/2) (by linarith)
  have hM0 : 0≤∑' k, ((gap k : ℝ))^2*(prime k : ℝ)^(-(3/2:ℝ)) :=
    tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (prime_pos_real k).le _)
  refine ⟨8+∑' k, ((gap k : ℝ))^2*(prime k : ℝ)^(-(3/2:ℝ)), fun t => ?_⟩
  set M := ∑' k, ((gap k : ℝ))^2*(prime k : ℝ)^(-(3/2:ℝ))
  set s : ℂ := 1/2+t*I with hsdef
  have hre : s.re=1/2 := by simp [hsdef]
  have him : s.im=t := by simp [hsdef]
  have hne : s≠1 := fun h' => by rw [h', Complex.one_re] at hre; norm_num at hre
  have hnorm_s : ‖s‖≤1/2+|t| := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [hre, him, abs_of_pos (by norm_num : (0:ℝ)<1/2)] at this
    exact this
  have hs1 : (1/2:ℝ)≤ ‖s-1‖ := by
    have hr : (s-1).re=-(1/2) := by rw [Complex.sub_re, hre, Complex.one_re]; norm_num
    have := Complex.abs_re_le_norm (s-1)
    rw [hr, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<1/2)] at this
    exact this
  have hs1pos : 0< ‖s-1‖ := by linarith
  have hA : ‖1/(s-1)‖≤2 := by
    rw [norm_div, norm_one, div_le_iff₀ hs1pos]; linarith
  have hB : ‖gapPolar s‖≤6 := by
    rw [gapPolar, dslope_of_ne _ hne, slope_def_field, sub_self, Complex.cpow_zero, norm_div,
      div_le_iff₀ hs1pos]
    have h2 : ‖(2:ℂ)^(1-s)‖≤2 := by
      have e : (2:ℂ)=((2:ℕ):ℂ) := by norm_num
      rw [e, Complex.norm_natCast_cpow_of_pos (by norm_num), Complex.sub_re, Complex.one_re, hre]
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤ (2:ℕ))
        (by norm_num : (1:ℝ)-1/2≤1)
      rwa [Real.rpow_one] at this
    calc ‖(2:ℂ)^(1-s)-1‖≤ ‖(2:ℂ)^(1-s)‖+‖(1:ℂ)‖ := norm_sub_le _ _
      _≤6*‖s-1‖ := by rw [norm_one]; linarith
  have hC : ‖gapRegular s‖≤ ‖s‖*M := by
    refine tsum_of_norm_bounded (hsum.hasSum.mul_left ‖s‖) (fun k => ?_)
    have := norm_gapRemainder_le k (s := s) (by rw [hre]; norm_num)
    rw [hre, show -(1/2:ℝ)-1=-(3/2:ℝ) by norm_num] at this
    linarith [this]
  have hsM : ‖s‖*M≤ (1/2+|t|)*M := mul_le_mul_of_nonneg_right hnorm_s hM0
  calc ‖gapDirichletCont s‖≤ ‖1/(s-1)‖+(‖gapPolar s‖+‖gapRegular s‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _≤ (8+M)*(1+|t|) := by nlinarith [abs_nonneg t]

/-! ### Unconditional instance -/

/-- **Unconditional continuation.**  `D(s) = 1/(s - 1) + G(s)` with `G` holomorphic on
`Re s > 71/100`; the continuation has a simple pole of residue `1` at `s = 1`. -/
theorem gapDirichlet_continuation_hoheisel :
    (∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | 71/100< s.re} ∧
      ∀ s : ℂ, 1< s.re → gapDirichlet s=1/(s-1)+G s) ∧
    Tendsto (fun s => (s-1)*gapDirichletCont s) (𝓝[≠] 1) (𝓝 1) :=
  ⟨exists_gapDirichlet_continuation gapMomentBound_hoheisel,
    tendsto_sub_one_mul_gapDirichletCont gapMomentBound_hoheisel (by norm_num)⟩

end

end RHTower.PrimeGapDirichlet
