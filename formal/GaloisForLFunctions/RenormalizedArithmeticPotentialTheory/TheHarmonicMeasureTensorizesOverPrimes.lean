import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRoughHarmonicMeasureHasThinShells
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass

/-!
# The harmonic measure tensorizes over primes

The harmonic measure `μ(n) = 1/n` on `[1, X]` is not a product over primes: the horizon `n ≤ X`
couples the valuations. It is nonetheless a product up to a bounded constant (approximate
Efron–Stein): there is `C` such that for every `X` and every `f`,

  `Var_μ(f) ≤ C Σ_{q ≤ X} Σ_{u ≤ X, q ∤ u} Var_{q-ladder of u}(f)`
  (`exists_harmonicVar_le_glauberForm`),

with unnormalized variances and the harmonic weights on each ladder `{u q^j ≤ X}`.

**Proof.** Peel the smallest prime `p` from the `p`-rough numbers `R(p, X) = ⊔_j p^j R(p+1, X/p^j)`
(`peel`). Within the levels, induction. Between the levels, split `f(p^j K) = g(K) + h` with `g` the
ladder mean: the `h`-part costs `(1 + η)` times the `p`-ladder variances (Jensen); the `g`-part costs
`(1 + 1/η) τ(p, X) Var(f)`, since the level means of `g` are means over nested sets
(`mul_sq_wMean_sub_le`) and `τ(p, X)` is the mass they lose to the horizon. The shell rate
`τ(p, X) ≤ C log p/(p log X)` (`TheRoughHarmonicMeasureHasThinShells`) is paid by the potential
`Ψ(Q, X) = −A Σ_{q < Q} (log q/q)/log X`, which drops by `A log p/(p log X)` along every peeling
step and stays in `[−3A, 0]` by Mertens' first theorem.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### 1. Weighted variance -/

section WeightedVariance

variable {ι : Type*} (s : Finset ι) (w v : ι → ℝ)

/-- The weighted mean `Σ w v/Σ w`. -/
def wMean : ℝ := (∑ i ∈ s, w i * v i) / ∑ i ∈ s, w i

/-- The (unnormalized) weighted variance `Σ w (v − mean)²`. -/
def wVar : ℝ := ∑ i ∈ s, w i * (v i - wMean s w v) ^ 2

variable {s w v}

theorem wVar_nonneg (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ wVar s w v :=
  sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)

theorem sum_mul_sub_wMean (hw : ∀ i ∈ s, 0 ≤ w i) : ∑ i ∈ s, w i * (v i - wMean s w v) = 0 := by
  by_cases hW : ∑ i ∈ s, w i = 0
  · have h0 := (sum_eq_zero_iff_of_nonneg hw).mp hW
    exact sum_eq_zero fun i hi => by rw [h0 i hi, zero_mul]
  · have e : (∑ i ∈ s, w i) * ((∑ i ∈ s, w i * v i) / ∑ i ∈ s, w i) = ∑ i ∈ s, w i * v i := by
      field_simp
    rw [sum_congr rfl fun i _ => mul_sub (w i) (v i) (wMean s w v), sum_sub_distrib, ← sum_mul,
      wMean, e, sub_self]

/-- **Steiner's identity**: `Σ w (v − c)² = Var + (Σ w)(mean − c)²`. -/
theorem sum_mul_sub_sq_eq (hw : ∀ i ∈ s, 0 ≤ w i) (c : ℝ) :
    ∑ i ∈ s, w i * (v i - c) ^ 2 = wVar s w v + (∑ i ∈ s, w i) * (wMean s w v - c) ^ 2 := by
  have h0 := sum_mul_sub_wMean (v := v) hw
  set m := wMean s w v
  have e : ∀ i, w i * (v i - c) ^ 2 =
      w i * (v i - m) ^ 2 + 2 * (m - c) * (w i * (v i - m)) + w i * (m - c) ^ 2 := fun i => by ring
  rw [sum_congr rfl fun i _ => e i, sum_add_distrib, sum_add_distrib, ← mul_sum, h0, ← sum_mul,
    wVar]
  ring

theorem wVar_le (hw : ∀ i ∈ s, 0 ≤ w i) (c : ℝ) : wVar s w v ≤ ∑ i ∈ s, w i * (v i - c) ^ 2 := by
  rw [sum_mul_sub_sq_eq hw c]
  have : 0 ≤ ∑ i ∈ s, w i := sum_nonneg hw
  nlinarith [sq_nonneg (wMean s w v - c)]

/-- **Jensen**: `(Σ w)(mean − c)² ≤ Σ w (v − c)²`. -/
theorem sum_mul_sq_wMean_sub_le (hw : ∀ i ∈ s, 0 ≤ w i) (c : ℝ) :
    (∑ i ∈ s, w i) * (wMean s w v - c) ^ 2 ≤ ∑ i ∈ s, w i * (v i - c) ^ 2 := by
  rw [sum_mul_sub_sq_eq hw c]
  linarith [wVar_nonneg (v := v) hw]

/-- **Weighted Cauchy–Schwarz**: `(Σ w d)² ≤ (Σ w)(Σ w d²)`. -/
theorem sq_sum_mul_le (hw : ∀ i ∈ s, 0 ≤ w i) (d : ι → ℝ) :
    (∑ i ∈ s, w i * d i) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * d i ^ 2 := by
  by_cases hW : ∑ i ∈ s, w i = 0
  · have h0 := (sum_eq_zero_iff_of_nonneg hw).mp hW
    rw [sum_eq_zero fun i hi => by rw [h0 i hi, zero_mul], hW]
    simp
  · have hWpos : 0 < ∑ i ∈ s, w i := lt_of_le_of_ne (sum_nonneg hw) (Ne.symm hW)
    have hJ := sum_mul_sq_wMean_sub_le (v := d) hw 0
    simp only [sub_zero] at hJ
    rw [wMean] at hJ
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)] at hJ
    nlinarith

theorem wMean_add (v' : ι → ℝ) : wMean s w (fun i => v i + v' i) = wMean s w v + wMean s w v' := by
  simp only [wMean, mul_add, sum_add_distrib, add_div]

theorem wVar_const_mul {a : ℝ} (ha : a ≠ 0) : wVar s (fun i => a * w i) v = a * wVar s w v := by
  have hm : wMean s (fun i => a * w i) v = wMean s w v := by
    simp only [wMean, mul_assoc, ← mul_sum]
    by_cases hW : ∑ i ∈ s, w i = 0
    · rw [hW, mul_zero, div_zero, div_zero]
    · exact mul_div_mul_left _ _ ha
  rw [wVar, hm, wVar, mul_sum]
  exact sum_congr rfl fun i _ => by ring

theorem wVar_congr {s' : Finset ι} {w' v' : ι → ℝ} (hs : s = s') (hwv : ∀ i ∈ s, w i = w' i)
    (hv : ∀ i ∈ s, v i = v' i) : wVar s w v = wVar s' w' v' := by
  subst hs
  have hm : wMean s w v = wMean s w' v' := by
    rw [wMean, wMean, sum_congr rfl hwv, sum_congr rfl fun i hi => by rw [hwv i hi, hv i hi]]
  rw [wVar, wVar, hm]
  exact sum_congr rfl fun i hi => by rw [hwv i hi, hv i hi]

/-- A variance supported on one point vanishes. -/
theorem wVar_eq_zero_of_subsingleton (hw : ∀ i ∈ s, 0 ≤ w i) {i₀ : ι}
    (hs : ∀ i ∈ s, i = i₀) : wVar s w v = 0 := by
  refine le_antisymm ((wVar_le hw (v i₀)).trans (le_of_eq ?_)) (wVar_nonneg hw)
  exact sum_eq_zero fun i hi => by rw [hs i hi, sub_self, sq, mul_zero, mul_zero]

/-- **Nested means.** For `A ⊆ s` with `Σ_A w > 0`:
`(Σ_A w)(mean_A − mean_s)² (Σ_s w) ≤ Var_s (Σ_s w − Σ_A w)`. -/
theorem mul_sq_wMean_sub_le (hw : ∀ i ∈ s, 0 ≤ w i) {A : Finset ι} (hA : A ⊆ s)
    (hWA : 0 < ∑ i ∈ A, w i) :
    (∑ i ∈ A, w i) * (wMean A w v - wMean s w v) ^ 2 * (∑ i ∈ s, w i) ≤
      wVar s w v * ((∑ i ∈ s, w i) - ∑ i ∈ A, w i) := by
  classical
  set m := wMean s w v
  set d : ι → ℝ := fun i => v i - m
  have hwA : ∀ i ∈ A, 0 ≤ w i := fun i hi => hw i (hA hi)
  have hwB : ∀ i ∈ s \ A, 0 ≤ w i := fun i hi => hw i (mem_sdiff.mp hi).1
  set σ := ∑ i ∈ A, w i * d i
  set WA := ∑ i ∈ A, w i
  set WB := ∑ i ∈ s \ A, w i
  have hsplit : ∀ φ : ι → ℝ, ∑ i ∈ s, φ i = ∑ i ∈ s \ A, φ i + ∑ i ∈ A, φ i :=
    fun φ => (sum_sdiff hA).symm
  have hσB : ∑ i ∈ s \ A, w i * d i = -σ := by
    have h0 := sum_mul_sub_wMean (v := v) hw
    rw [hsplit] at h0
    linarith
  have hmeanA : WA * (wMean A w v - m) = σ := by
    rw [wMean, mul_sub, mul_div_cancel₀ _ hWA.ne']
    simp only [σ, d, mul_sub, sum_sub_distrib, ← sum_mul, WA]
  have hCA := sq_sum_mul_le hwA d
  have hCB := sq_sum_mul_le hwB d
  rw [hσB, neg_sq] at hCB
  have hV : wVar s w v = ∑ i ∈ s \ A, w i * d i ^ 2 + ∑ i ∈ A, w i * d i ^ 2 := hsplit _
  have hWs : ∑ i ∈ s, w i = WB + WA := hsplit _
  have hWB0 : 0 ≤ WB := sum_nonneg hwB
  have hlhs : WA * (wMean A w v - m) ^ 2 * (WB + WA) * WA = σ ^ 2 * (WB + WA) := by
    rw [← hmeanA]; ring
  have key : σ ^ 2 * (WB + WA) ≤ WA * WB * (∑ i ∈ s \ A, w i * d i ^ 2 + ∑ i ∈ A, w i * d i ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hCA hWB0, mul_le_mul_of_nonneg_left hCB hWA.le]
  rw [hWs, hV, show WB + WA - WA = WB by ring]
  have h2 : WA * (wMean A w v - m) ^ 2 * (WB + WA) * WA ≤
      (∑ i ∈ s \ A, w i * d i ^ 2 + ∑ i ∈ A, w i * d i ^ 2) * WB * WA := by
    rw [hlhs]; linarith
  exact le_of_mul_le_mul_right h2 hWA

end WeightedVariance

/-- `(x + y)² ≤ (1 + η) x² + (1 + 1/η) y²`. -/
theorem add_sq_le_of_pos {η : ℝ} (hη : 0 < η) (x y : ℝ) :
    (x + y) ^ 2 ≤ (1 + η) * x ^ 2 + (1 + 1 / η) * y ^ 2 := by
  have h : 0 ≤ (η * x - y) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
  have e : (η * x - y) ^ 2 / η = η * x ^ 2 - 2 * x * y + y ^ 2 / η := by
    field_simp; ring
  rw [e] at h
  have : (1 + 1 / η) * y ^ 2 = y ^ 2 + y ^ 2 / η := by ring
  nlinarith

/-! ### 2. Ladders and the Glauber form -/

/-- The `q`-ladder of `u` in `[1, X]`: exponents `j` with `u q^j ≤ X`. -/
def ladder (q u X : ℕ) : Finset ℕ := (range (X + 1)).filter fun j => u * q ^ j ≤ X

/-- The harmonic weights `1/(u q^j)` on a ladder. -/
def ladderWeight (q u : ℕ) (j : ℕ) : ℝ := 1 / ((u * q ^ j : ℕ) : ℝ)

/-- The variance of `f` along the `q`-ladder of `u`, harmonic weights. -/
def ladderVar (q u X : ℕ) (f : ℕ → ℝ) : ℝ :=
  wVar (ladder q u X) (ladderWeight q u) (fun j => f (u * q ^ j))

/-- The mean of `f` along the `q`-ladder of `u`. -/
def ladderMean (q u X : ℕ) (f : ℕ → ℝ) : ℝ :=
  wMean (ladder q u X) (ladderWeight q u) (fun j => f (u * q ^ j))

/-- The variance of `f` under the harmonic measure on the `Q`-rough numbers of `[1, X]`. -/
def harmonicVar (Q X : ℕ) (f : ℕ → ℝ) : ℝ := wVar (roughInterval Q X) (fun n => 1 / (n : ℝ)) f

/-- The **Glauber form**: the sum over primes `q ≥ Q` of the `q`-ladder variances. -/
def glauberForm (Q X : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ q ∈ (Icc Q X).filter Nat.Prime,
    ∑ u ∈ (roughInterval Q X).filter (fun u => ¬ q ∣ u), ladderVar q u X f

theorem ladderWeight_nonneg (q u j : ℕ) : 0 ≤ ladderWeight q u j :=
  div_nonneg zero_le_one (Nat.cast_nonneg _)

theorem ladderVar_nonneg (q u X : ℕ) (f : ℕ → ℝ) : 0 ≤ ladderVar q u X f :=
  wVar_nonneg fun j _ => ladderWeight_nonneg q u j

theorem glauberForm_nonneg (Q X : ℕ) (f : ℕ → ℝ) : 0 ≤ glauberForm Q X f :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => ladderVar_nonneg _ _ _ _

theorem harmonicVar_nonneg (Q X : ℕ) (f : ℕ → ℝ) : 0 ≤ harmonicVar Q X f :=
  wVar_nonneg fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n)

/-- On a rough interval that is at most `{1}` the variance vanishes. -/
theorem harmonicVar_eq_zero_of_le_one {Q X : ℕ} (h : ∀ K ∈ roughInterval Q X, K = 1)
    (f : ℕ → ℝ) : harmonicVar Q X f = 0 :=
  wVar_eq_zero_of_subsingleton (fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n)) h

theorem eq_one_of_mem_roughInterval_of_le {Q X K : ℕ} (hK : K ∈ roughInterval Q X) (hX : X < Q) :
    K = 1 := by
  by_contra h
  have h1 := (mem_roughInterval.mp hK).1
  have := lt_of_mem_roughInterval hK (by omega)
  have := (mem_roughInterval.mp hK).2.1
  omega

theorem zero_mem_ladder {q u X : ℕ} (hu : u ≤ X) : 0 ∈ ladder q u X :=
  mem_filter.mpr ⟨mem_range.mpr (Nat.succ_pos X), by simpa using hu⟩

theorem mem_ladder {q u X j : ℕ} (hq : 2 ≤ q) (hu : 1 ≤ u) : j ∈ ladder q u X ↔ u * q ^ j ≤ X := by
  refine ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_range.mpr ?_, h⟩⟩
  have h1 : j < q ^ j := Nat.lt_pow_self (by omega)
  have h2 : q ^ j ≤ u * q ^ j := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- Above the horizon a ladder is the single point `j = 0`. -/
theorem ladderVar_eq_zero_of_lt {q u Y : ℕ} (hq : 2 ≤ q) (hu : 1 ≤ u) (hY : Y < q)
    (f : ℕ → ℝ) : ladderVar q u Y f = 0 := by
  refine wVar_eq_zero_of_subsingleton (fun j _ => ladderWeight_nonneg q u j) (i₀ := 0) fun j hj => ?_
  rw [mem_ladder hq hu] at hj
  by_contra hj0
  have : q ≤ q ^ j := Nat.le_self_pow hj0 q
  have : q ^ j ≤ u * q ^ j := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- Scaling a ladder by `p^j`. -/
theorem ladderVar_mul_pow {p q K j X : ℕ} (hp : 0 < p) (hq : 2 ≤ q) (hK : 1 ≤ K) (f : ℕ → ℝ) :
    ladderVar q (p ^ j * K) X f = (1 / (p : ℝ)) ^ j * ladderVar q K (X / p ^ j) (fun n => f (p ^ j * n)) := by
  have hpj : 0 < p ^ j := pow_pos hp j
  rw [ladderVar, ladderVar, ← wVar_const_mul (pow_ne_zero _ (by positivity))]
  refine wVar_congr ?_ (fun i _ => ?_) (fun i _ => by rw [mul_assoc])
  · ext i
    rw [mem_ladder hq (by simpa using Nat.mul_le_mul (Nat.one_le_pow j p hp) hK), mem_ladder hq hK,
      Nat.le_div_iff_mul_le hpj]
    constructor <;> intro h <;> linarith [mul_comm (p ^ j) (K * q ^ i), mul_assoc (p ^ j) K (q ^ i)]
  · simp only [ladderWeight]
    push_cast
    rw [one_div_pow, one_div_mul_one_div, mul_assoc]

/-- `{u ∈ R(p, X) : p ∤ u} = R(p + 1, X)`. -/
theorem roughInterval_filter_not_dvd {p : ℕ} (hp : p.Prime) (X : ℕ) :
    (roughInterval p X).filter (fun u => ¬ p ∣ u) = roughInterval (p + 1) X := by
  ext u
  simp only [mem_filter, mem_roughInterval]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, h2, fun q hq hd => ?_⟩
    have := h3 q hq hd
    rcases this.lt_or_eq with h | h
    · omega
    · exact absurd (h ▸ hd) h4
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2, fun q hq hd => (h3 q hq hd).trans' (by omega)⟩, fun hd => ?_⟩
    have := h3 p hp hd
    omega

/-- **Ladders versus levels**: summing over the levels `R(p+1, X/p^j)` is summing over the
`p`-ladders of `R(p+1, X)`. -/
theorem sum_levels_eq_sum_ladders {p : ℕ} (hp : p.Prime) (X : ℕ) (ψ : ℕ → ℕ → ℝ) :
    ∑ j ∈ range (X + 1), ∑ K ∈ roughInterval (p + 1) (X / p ^ j), ψ j K =
      ∑ K ∈ roughInterval (p + 1) X, ∑ j ∈ ladder p K X, ψ j K := by
  refine sum_comm' fun j K => ?_
  simp only [mem_range, mem_roughInterval, ladder, mem_filter]
  rw [Nat.le_div_iff_mul_le (pow_pos hp.pos j)]
  constructor
  · rintro ⟨hj, h1, h2, h3⟩
    exact ⟨⟨hj, h2⟩, h1, (Nat.le_mul_of_pos_right K (pow_pos hp.pos j)).trans h2, h3⟩
  · rintro ⟨⟨hj, h2⟩, h1, -, h3⟩
    exact ⟨hj, h1, h2, h3⟩

/-- The rough numbers as a union of `p`-ladders. -/
theorem sum_roughInterval_eq_sum_ladders {p : ℕ} (hp : p.Prime) (X : ℕ) (φ : ℕ → ℝ) :
    ∑ n ∈ roughInterval p X, φ n = ∑ K ∈ roughInterval (p + 1) X, ∑ j ∈ ladder p K X, φ (K * p ^ j) := by
  rw [sum_roughInterval_eq_levels hp, sum_levels_eq_sum_ladders hp X (fun j K => φ (p ^ j * K))]
  exact sum_congr rfl fun K _ => sum_congr rfl fun j _ => by rw [mul_comm]

/-- **Splitting the Glauber form at `p`**: the `p`-ladders plus the levels. -/
theorem glauberForm_eq_levels {p : ℕ} (hp : p.Prime) {X : ℕ} (hpX : p ≤ X) (f : ℕ → ℝ) :
    glauberForm p X f = ∑ K ∈ roughInterval (p + 1) X, ladderVar p K X f +
      ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j *
        glauberForm (p + 1) (X / p ^ j) (fun n => f (p ^ j * n)) := by
  have hins : (Icc p X).filter Nat.Prime = insert p ((Icc (p + 1) X).filter Nat.Prime) := by
    ext q
    simp only [mem_filter, mem_Icc, mem_insert]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases h1.lt_or_eq with h | h
      · exact Or.inr ⟨⟨h, h2⟩, h3⟩
      · exact Or.inl h.symm
    · rintro (h | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h ▸ le_rfl, h ▸ hpX⟩, h ▸ hp⟩
      · exact ⟨⟨by omega, h2⟩, h3⟩
  have hnot : p ∉ (Icc (p + 1) X).filter Nat.Prime := fun h => by
    have := (mem_Icc.mp (mem_filter.mp h).1).1; omega
  rw [glauberForm, hins, sum_insert hnot, roughInterval_filter_not_dvd hp]
  congr 1
  -- the primes `q > p`, level by level
  have hq : ∀ q ∈ (Icc (p + 1) X).filter Nat.Prime,
      ∑ u ∈ (roughInterval p X).filter (fun u => ¬ q ∣ u), ladderVar q u X f =
        ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j *
          ∑ K ∈ (roughInterval (p + 1) (X / p ^ j)).filter (fun u => ¬ q ∣ u),
            ladderVar q K (X / p ^ j) (fun n => f (p ^ j * n)) := by
    intro q hq
    obtain ⟨hqI, hqp⟩ := mem_filter.mp hq
    have hpq : p + 1 ≤ q := (mem_Icc.mp hqI).1
    rw [sum_filter, sum_roughInterval_eq_levels hp]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_filter, mul_sum]
    refine sum_congr rfl fun K hK => ?_
    have hK1 := (mem_roughInterval.mp hK).1
    have hdvd : q ∣ p ^ j * K ↔ q ∣ K := by
      constructor
      · intro h
        rcases (Nat.Prime.dvd_mul hqp).mp h with h' | h'
        · have := (Nat.prime_dvd_prime_iff_eq hqp hp).mp (hqp.dvd_of_dvd_pow h'); omega
        · exact h'
      · exact fun h => h.mul_left _
    by_cases hqK : q ∣ K
    · rw [if_neg (not_not.mpr (hdvd.mpr hqK)), if_neg (not_not.mpr hqK), mul_zero]
    · rw [if_pos (fun h => hqK (hdvd.mp h)), if_pos hqK]
      exact ladderVar_mul_pow hp.pos hqp.two_le hK1 f
  rw [sum_congr rfl hq, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum, glauberForm]
  congr 1
  symm
  refine sum_subset (fun q hq => ?_) (fun q hq hq' => ?_)
  · obtain ⟨h1, h2⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp h1).1, (mem_Icc.mp h1).2.trans
      (Nat.div_le_self _ _)⟩, h2⟩
  · obtain ⟨h1, h2⟩ := mem_filter.mp hq
    have hlt : X / p ^ j < q := by
      by_contra h
      exact hq' (mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp h1).1, by omega⟩, h2⟩)
    exact sum_eq_zero fun K hK => ladderVar_eq_zero_of_lt h2.two_le
      (mem_roughInterval.mp (mem_filter.mp hK).1).1 hlt _

/-! ### 3. Peeling one prime -/

/-- **Peeling `p`.** If every level `R(p+1, X/p^j)` satisfies the tensorization with constant `B`,
then `(1 − (1 + 1/η) τ(p, X)) Var ≤ max(B, 1 + η) · Glauber` on `R(p, X)`. -/
theorem peel {p : ℕ} (hp : p.Prime) {X : ℕ} (hpX : p ≤ X) (f : ℕ → ℝ) {η B : ℝ} (hη : 0 < η)
    (hB : 0 ≤ B)
    (hlev : ∀ j ∈ range (X + 1), harmonicVar (p + 1) (X / p ^ j) (fun K => f (p ^ j * K)) ≤
      B * glauberForm (p + 1) (X / p ^ j) (fun K => f (p ^ j * K))) :
    (1 - (1 + 1 / η) * shellTau p X) * harmonicVar p X f ≤ max B (1 + η) * glauberForm p X f := by
  have hμ : ∀ n : ℕ, (0 : ℝ) ≤ 1 / (n : ℝ) := fun n => by positivity
  have hr : ∀ j : ℕ, (0 : ℝ) ≤ (1 / (p : ℝ)) ^ j := fun j => by positivity
  have hX1 : 1 ≤ X := by have := hp.two_le; omega
  set g : ℕ → ℝ := fun K => ladderMean p K X f with hg
  set c := wMean (roughInterval (p + 1) X) (fun n => 1 / (n : ℝ)) g with hc
  set V := harmonicVar p X f with hV
  set Gp := ∑ K ∈ roughInterval (p + 1) X, ladderVar p K X f with hGp_def
  set Glev := ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j *
    glauberForm (p + 1) (X / p ^ j) (fun n => f (p ^ j * n)) with hGlev_def
  have hG : glauberForm p X f = Gp + Glev := glauberForm_eq_levels hp hpX f
  have hGp : 0 ≤ Gp := sum_nonneg fun _ _ => ladderVar_nonneg _ _ _ _
  have hGlev : 0 ≤ Glev :=
    sum_nonneg fun j _ => mul_nonneg (hr j) (glauberForm_nonneg _ _ _)
  -- the level quantities
  have hF : ∀ j, 0 ≤ roughHarmonic (p + 1) (X / p ^ j) := fun j => roughHarmonic_nonneg _ _
  have hFsum : ∀ j, ∑ K ∈ roughInterval (p + 1) (X / p ^ j), 1 / (K : ℝ) =
      roughHarmonic (p + 1) (X / p ^ j) := fun j => rfl
  -- Step 1: Steiner on each level, with the common centre `c`
  have hstep1 : V ≤ ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j *
      (harmonicVar (p + 1) (X / p ^ j) (fun K => f (p ^ j * K)) +
        roughHarmonic (p + 1) (X / p ^ j) *
          (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ))
            (fun K => f (p ^ j * K)) - c) ^ 2) := by
    refine (wVar_le (fun n _ => hμ n) c).trans (le_of_eq ?_)
    rw [sum_roughInterval_eq_levels hp]
    refine sum_congr rfl fun j _ => ?_
    have hS := sum_mul_sub_sq_eq (s := roughInterval (p + 1) (X / p ^ j))
      (w := fun n => 1 / (n : ℝ)) (v := fun K => f (p ^ j * K)) (fun K _ => hμ K) c
    have e : ∑ K ∈ roughInterval (p + 1) (X / p ^ j),
        1 / ((p ^ j * K : ℕ) : ℝ) * (f (p ^ j * K) - c) ^ 2 =
        (1 / (p : ℝ)) ^ j * ∑ K ∈ roughInterval (p + 1) (X / p ^ j),
          1 / (K : ℝ) * (f (p ^ j * K) - c) ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun K _ => ?_
      push_cast
      rw [one_div_pow, ← mul_assoc, one_div_mul_one_div]
    rw [e, hS, hFsum]
    rfl
  -- Step 2: the levels, by hypothesis
  have hstep2 : ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j *
      harmonicVar (p + 1) (X / p ^ j) (fun K => f (p ^ j * K)) ≤ B * Glev := by
    rw [hGlev_def, mul_sum]
    exact sum_le_sum fun j hj => by
      have := mul_le_mul_of_nonneg_left (hlev j hj) (hr j)
      linarith
  -- Step 3: split each level mean into the `h`-part and the `g`-part
  have hmab : ∀ j, wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ))
      (fun K => f (p ^ j * K)) = wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ))
        (fun K => f (p ^ j * K) - g K) +
      wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ)) g := fun j => by
    have := wMean_add (s := roughInterval (p + 1) (X / p ^ j)) (w := fun n => 1 / (n : ℝ))
      (v := fun K => f (p ^ j * K) - g K) g
    simp only [sub_add_cancel] at this
    exact this
  -- Step 4: the `h`-part is the `p`-ladder variance
  have hstep4 : ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j * (roughHarmonic (p + 1) (X / p ^ j) *
      wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ))
        (fun K => f (p ^ j * K) - g K) ^ 2) ≤ Gp := by
    have h1 : ∀ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j * (roughHarmonic (p + 1) (X / p ^ j) *
        wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ))
          (fun K => f (p ^ j * K) - g K) ^ 2) ≤
        ∑ K ∈ roughInterval (p + 1) (X / p ^ j),
          (1 / (p : ℝ)) ^ j * (1 / (K : ℝ) * (f (p ^ j * K) - g K) ^ 2) := by
      intro j _
      have hJ := sum_mul_sq_wMean_sub_le (s := roughInterval (p + 1) (X / p ^ j))
        (w := fun n => 1 / (n : ℝ)) (v := fun K => f (p ^ j * K) - g K) (fun K _ => hμ K) 0
      simp only [sub_zero] at hJ
      rw [← mul_sum, ← hFsum]
      exact mul_le_mul_of_nonneg_left hJ (hr j)
    refine (sum_le_sum h1).trans (le_of_eq ?_)
    rw [sum_levels_eq_sum_ladders hp X (fun j K =>
      (1 / (p : ℝ)) ^ j * (1 / (K : ℝ) * (f (p ^ j * K) - g K) ^ 2)), hGp_def]
    refine sum_congr rfl fun K _ => ?_
    rw [ladderVar, wVar]
    refine sum_congr rfl fun j _ => ?_
    have e1 : (1 / (p : ℝ)) ^ j * (1 / (K : ℝ)) = ladderWeight p K j := by
      rw [ladderWeight]
      push_cast
      rw [one_div_pow, one_div_mul_one_div, mul_comm]
    rw [← mul_assoc, e1, mul_comm (p ^ j) K]
    rfl
  -- Step 5: the `g`-part costs the shell rate
  have hF0 : 0 < roughHarmonic (p + 1) X :=
    lt_of_lt_of_le one_pos (one_le_roughHarmonic (p + 1) hX1)
  have hstep5 : ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j * (roughHarmonic (p + 1) (X / p ^ j) *
      (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ)) g - c) ^ 2) ≤
      shellTau p X * wVar (roughInterval (p + 1) X) (fun n => 1 / (n : ℝ)) g := by
    rw [← sum_filter_add_sum_filter_not (range (X + 1)) (fun j => p ^ j ≤ X)]
    have hzero : ∑ j ∈ (range (X + 1)).filter (fun j => ¬ p ^ j ≤ X),
        (1 / (p : ℝ)) ^ j * (roughHarmonic (p + 1) (X / p ^ j) *
          (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ)) g - c) ^ 2) = 0 := by
      refine sum_eq_zero fun j hj => ?_
      have hlt : X / p ^ j = 0 := Nat.div_eq_of_lt (not_le.mp (mem_filter.mp hj).2)
      have : roughHarmonic (p + 1) (X / p ^ j) = 0 := by
        rw [hlt, roughHarmonic]
        exact sum_eq_zero fun K hK => absurd (mem_roughInterval.mp hK) (by omega)
      rw [this, zero_mul, mul_zero]
    rw [hzero, add_zero, shellTau, sum_mul]
    refine sum_le_sum fun j hj => ?_
    have hpj := (mem_filter.mp hj).2
    have hsub : roughInterval (p + 1) (X / p ^ j) ⊆ roughInterval (p + 1) X :=
      roughInterval_mono (Nat.div_le_self _ _)
    have hFj : 0 < roughHarmonic (p + 1) (X / p ^ j) :=
      lt_of_lt_of_le one_pos (one_le_roughHarmonic (p + 1)
        ((Nat.le_div_iff_mul_le (pow_pos hp.pos j)).mpr (by rw [one_mul]; exact hpj)))
    have hnest := mul_sq_wMean_sub_le (s := roughInterval (p + 1) X) (w := fun n => 1 / (n : ℝ))
      (v := g) (fun K _ => hμ K) hsub (by rw [hFsum]; exact hFj)
    rw [hFsum, show ∑ K ∈ roughInterval (p + 1) X, 1 / (K : ℝ) = roughHarmonic (p + 1) X from rfl]
      at hnest
    have key : roughHarmonic (p + 1) (X / p ^ j) *
        (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ)) g - c) ^ 2 ≤
        wVar (roughInterval (p + 1) X) (fun n => 1 / (n : ℝ)) g *
          ((roughHarmonic (p + 1) X - roughHarmonic (p + 1) (X / p ^ j)) /
            roughHarmonic (p + 1) X) := by
      rw [mul_div_assoc', le_div_iff₀ hF0]
      exact hnest
    calc (1 / (p : ℝ)) ^ j * (roughHarmonic (p + 1) (X / p ^ j) *
          (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ)) g - c) ^ 2)
        ≤ (1 / (p : ℝ)) ^ j * (wVar (roughInterval (p + 1) X) (fun n => 1 / (n : ℝ)) g *
          ((roughHarmonic (p + 1) X - roughHarmonic (p + 1) (X / p ^ j)) /
            roughHarmonic (p + 1) X)) := mul_le_mul_of_nonneg_left key (hr j)
      _ = (1 / (p : ℝ)) ^ j * ((roughHarmonic (p + 1) X - roughHarmonic (p + 1) (X / p ^ j)) /
            roughHarmonic (p + 1) X) * wVar (roughInterval (p + 1) X) (fun n => 1 / (n : ℝ)) g := by
          ring
  -- Step 6: the ladder means vary less than `f`
  have hstep6 : wVar (roughInterval (p + 1) X) (fun n => 1 / (n : ℝ)) g ≤ V := by
    set m := wMean (roughInterval p X) (fun n => 1 / (n : ℝ)) f
    refine (wVar_le (fun K _ => hμ K) m).trans ?_
    have hper : ∀ K ∈ roughInterval (p + 1) X, 1 / (K : ℝ) * (g K - m) ^ 2 ≤
        ∑ j ∈ ladder p K X, ladderWeight p K j * (f (K * p ^ j) - m) ^ 2 := by
      intro K hK
      have hKX := (mem_roughInterval.mp hK).2.1
      have hW : 1 / (K : ℝ) ≤ ∑ j ∈ ladder p K X, ladderWeight p K j := by
        have := single_le_sum (fun j _ => ladderWeight_nonneg p K j) (zero_mem_ladder (q := p) hKX)
        simpa [ladderWeight] using this
      have hJ := sum_mul_sq_wMean_sub_le (s := ladder p K X) (w := ladderWeight p K)
        (v := fun j => f (K * p ^ j)) (fun j _ => ladderWeight_nonneg p K j) m
      calc 1 / (K : ℝ) * (g K - m) ^ 2
          ≤ (∑ j ∈ ladder p K X, ladderWeight p K j) * (g K - m) ^ 2 :=
            mul_le_mul_of_nonneg_right hW (sq_nonneg _)
        _ ≤ _ := hJ
    refine (sum_le_sum hper).trans (le_of_eq ?_)
    rw [hV, harmonicVar, wVar,
      sum_roughInterval_eq_sum_ladders hp X (fun n => 1 / (n : ℝ) * (f n - m) ^ 2)]
    rfl
  -- assemble
  have hτ0 : 0 ≤ shellTau p X := shellTau_nonneg p X
  have h1η : 0 ≤ 1 + 1 / η := by positivity
  have hbetween : ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j * (roughHarmonic (p + 1) (X / p ^ j) *
      (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ))
        (fun K => f (p ^ j * K)) - c) ^ 2) ≤
      (1 + η) * Gp + (1 + 1 / η) * (shellTau p X * V) := by
    have hterm : ∀ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j * (roughHarmonic (p + 1) (X / p ^ j) *
        (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ))
          (fun K => f (p ^ j * K)) - c) ^ 2) ≤
        (1 + η) * ((1 / (p : ℝ)) ^ j * (roughHarmonic (p + 1) (X / p ^ j) *
          wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ))
            (fun K => f (p ^ j * K) - g K) ^ 2)) +
        (1 + 1 / η) * ((1 / (p : ℝ)) ^ j * (roughHarmonic (p + 1) (X / p ^ j) *
          (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ)) g - c) ^ 2)) := by
      intro j _
      rw [hmab j, add_sub_assoc]
      have h := mul_le_mul_of_nonneg_left (add_sq_le_of_pos hη
        (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ))
          (fun K => f (p ^ j * K) - g K))
        (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ)) g - c))
        (mul_nonneg (hr j) (hF j))
      nlinarith
    refine (sum_le_sum hterm).trans ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left hstep4 (by linarith))
      (mul_le_mul_of_nonneg_left (hstep5.trans (mul_le_mul_of_nonneg_left hstep6 hτ0)) h1η)
  have htotal : V ≤ B * Glev + ((1 + η) * Gp + (1 + 1 / η) * (shellTau p X * V)) := by
    refine hstep1.trans ?_
    rw [show ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j *
        (harmonicVar (p + 1) (X / p ^ j) (fun K => f (p ^ j * K)) +
          roughHarmonic (p + 1) (X / p ^ j) *
            (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ))
              (fun K => f (p ^ j * K)) - c) ^ 2) =
        ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j *
          harmonicVar (p + 1) (X / p ^ j) (fun K => f (p ^ j * K)) +
        ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j * (roughHarmonic (p + 1) (X / p ^ j) *
          (wMean (roughInterval (p + 1) (X / p ^ j)) (fun n => 1 / (n : ℝ))
            (fun K => f (p ^ j * K)) - c) ^ 2) by
      rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring]
    linarith
  have hmax : B * Glev + (1 + η) * Gp ≤ max B (1 + η) * glauberForm p X f := by
    rw [hG]
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left B (1 + η)) hGlev,
      mul_le_mul_of_nonneg_right (le_max_right B (1 + η)) hGp]
  nlinarith

/-! ### 4. The induction over primes -/

theorem primesBelow_succ_eq (n : ℕ) :
    Nat.primesBelow (n + 1) = if n.Prime then insert n (Nat.primesBelow n) else Nat.primesBelow n := by
  simp only [Nat.primesBelow, range_add_one, filter_insert]

/-- **Tensorization of the rough harmonic measures.** There is `C` such that for every roughness `Q`,
every `X` and every `f`, `Var_{1/n, R(Q, X)}(f) ≤ C Σ_{q ≥ Q} Σ_{u, q ∤ u} Var_{q-ladder of u}(f)`. -/
theorem exists_harmonicVar_le_glauberForm_rough :
    ∃ C : ℝ, 0 < C ∧ ∀ Q X : ℕ, ∀ f : ℕ → ℝ, harmonicVar Q X f ≤ C * glauberForm Q X f := by
  obtain ⟨Cτ, hCτ1, hτ⟩ := exists_shellTau_le
  set η := 4 * Cτ
  have hη : 0 < η := by positivity
  set δs := (4 * Cτ + 1) / (4 * Cτ + 2)
  set A := (1 + 1 / η) * Cτ * (4 * Cτ + 2)
  have hA : 0 ≤ A := by positivity
  set K := (1 + η) * Real.exp (3 * A)
  have hK : 0 < K := by positivity
  set S : ℕ → ℝ := fun Q => ∑ q ∈ Nat.primesBelow Q, Real.log q / q
  have hS0 : ∀ Q, 0 ≤ S Q := fun Q => sum_nonneg fun q _ => div_nonneg
    (Real.log_natCast_nonneg q) (Nat.cast_nonneg q)
  set Ψ : ℕ → ℕ → ℝ := fun Q X => -A * S Q / Real.log X
  -- the claim, by strong induction on `X + 1 − Q`
  have claim : ∀ k Q X, X + 1 - Q ≤ k → 2 ≤ X → ∀ f : ℕ → ℝ,
      harmonicVar Q X f ≤ K * Real.exp (Ψ Q X) * glauberForm Q X f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro Q X hk hX f
    have hlX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hRHS : 0 ≤ K * Real.exp (Ψ Q X) * glauberForm Q X f :=
      mul_nonneg (by positivity) (glauberForm_nonneg _ _ _)
    by_cases hQX : X < Q
    · rw [harmonicVar_eq_zero_of_le_one (fun K hK => eq_one_of_mem_roughInterval_of_le hK hQX)]
      exact hRHS
    rw [not_lt] at hQX
    by_cases hQ : Q.Prime
    · -- peel `p = Q`
      have hp2 := hQ.two_le
      set p := Q
      set Bc := K * Real.exp (-A * S (p + 1) / Real.log X)
      have hBc : 0 ≤ Bc := by positivity
      have hSp : S (p + 1) = S p + Real.log p / p := by
        simp only [S, primesBelow_succ_eq, if_pos hQ]
        rw [sum_insert (fun h => by simp [Nat.primesBelow] at h)]
        ring
      -- the level bound
      have hlev : ∀ j ∈ range (X + 1), harmonicVar (p + 1) (X / p ^ j) (fun K => f (p ^ j * K)) ≤
          Bc * glauberForm (p + 1) (X / p ^ j) (fun K => f (p ^ j * K)) := by
        intro j _
        set Y := X / p ^ j
        by_cases hY : Y ≤ p
        · rw [harmonicVar_eq_zero_of_le_one (fun K hK => eq_one_of_mem_roughInterval_of_le hK
            (by omega))]
          exact mul_nonneg hBc (glauberForm_nonneg _ _ _)
        · have hYX : Y ≤ X := Nat.div_le_self _ _
          have hih := ih (Y + 1 - (p + 1)) (by omega) (p + 1) Y le_rfl (by omega)
            (fun K => f (p ^ j * K))
          refine hih.trans (mul_le_mul_of_nonneg_right ?_ (glauberForm_nonneg _ _ _))
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK.le
          have hlY : 0 < Real.log Y := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
          have hlYX : Real.log Y ≤ Real.log X :=
            Real.log_le_log (by exact_mod_cast (show 0 < Y by omega)) (by exact_mod_cast hYX)
          simp only [Ψ]
          rw [div_le_div_iff₀ hlY hlX]
          have := mul_nonneg (mul_nonneg hA (hS0 (p + 1))) (sub_nonneg.mpr hlYX)
          nlinarith
      -- the shell rate
      obtain ⟨hτ1, hτ2⟩ := hτ p X hQ hQX
      have hτ0 := shellTau_nonneg p X
      set δ := (1 + 1 / η) * shellTau p X
      have hδ0 : 0 ≤ δ := by positivity
      have hδs : δ ≤ δs := by
        have e : (1 + 1 / η) * (1 - 1 / (1 + 2 * Cτ)) = δs := by
          simp only [δs, η]; field_simp; ring
        calc δ ≤ (1 + 1 / η) * (1 - 1 / (1 + 2 * Cτ)) :=
              mul_le_mul_of_nonneg_left hτ2 (by positivity)
          _ = δs := e
      have hδs1 : 1 - δs = 1 / (4 * Cτ + 2) := by
        simp only [δs]; field_simp; ring
      have hδ1 : 0 < 1 - δ := by
        have : δs < 1 := by
          have : 0 < 1 / (4 * Cτ + 2) := by positivity
          linarith
        linarith
      have hδA : δ / (1 - δs) ≤ A * (Real.log p / (p * Real.log X)) := by
        rw [hδs1, div_div_eq_mul_div, div_one]
        have h := mul_le_mul_of_nonneg_left hτ1 (show 0 ≤ 1 + 1 / η by positivity)
        have hpos : 0 ≤ Real.log p / (p * Real.log X) := by
          have : 0 ≤ Real.log p := Real.log_natCast_nonneg p
          positivity
        calc δ * (4 * Cτ + 2) ≤ (1 + 1 / η) * (Cτ * (Real.log p / (p * Real.log X))) *
              (4 * Cτ + 2) := mul_le_mul_of_nonneg_right h (by positivity)
          _ = A * (Real.log p / (p * Real.log X)) := by simp only [A]; ring
      -- `B ≥ 1 + η`
      have hBη : 1 + η ≤ Bc := by
        have hm := RHTower.mertens_first_upper (n := p) (by have := hQ.two_le; omega)
        have hSle : S (p + 1) ≤ Real.log p + Real.log 4 := hm
        have hlp : Real.log p ≤ Real.log X :=
          Real.log_le_log (by exact_mod_cast hQ.pos) (by exact_mod_cast hQX)
        have hl2 : Real.log 2 ≤ Real.log X :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hX)
        have hl4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        have h3 : S (p + 1) / Real.log X ≤ 3 := by
          rw [div_le_iff₀ hlX]
          nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
        have : 0 ≤ 3 * A + -A * S (p + 1) / Real.log X := by
          rw [neg_mul, neg_div, mul_div_assoc]
          nlinarith
        calc 1 + η = (1 + η) * 1 := (mul_one _).symm
          _ ≤ (1 + η) * Real.exp (3 * A + -A * S (p + 1) / Real.log X) :=
              mul_le_mul_of_nonneg_left (Real.one_le_exp this) (by positivity)
          _ = Bc := by simp only [Bc, K]; rw [Real.exp_add]; ring
      have hpeel := peel hQ hQX f hη hBc hlev
      rw [max_eq_left hBη] at hpeel
      -- `V ≤ B/(1 − δ) G ≤ B e^{δ/(1−δ*)} G ≤ K e^{Ψ} G`
      have hV : harmonicVar p X f ≤ Bc / (1 - δ) * glauberForm p X f := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ1]
        linarith
      have hexp : 1 / (1 - δ) ≤ Real.exp (A * (Real.log p / (p * Real.log X))) := by
        have h1 : 1 / (1 - δ) = 1 + δ / (1 - δ) := by field_simp; ring
        have h2 : δ / (1 - δ) ≤ δ / (1 - δs) :=
          div_le_div_of_nonneg_left hδ0 (by
            have : 0 < 1 / (4 * Cτ + 2) := by positivity
            linarith) (by linarith)
        rw [h1]
        linarith [Real.add_one_le_exp (A * (Real.log p / (p * Real.log X)))]
      have hBK : Bc * Real.exp (A * (Real.log p / (p * Real.log X))) = K * Real.exp (Ψ p X) := by
        simp only [Bc, Ψ, mul_assoc, ← Real.exp_add]
        congr 2
        rw [hSp]
        field_simp
        ring
      calc harmonicVar p X f ≤ Bc / (1 - δ) * glauberForm p X f := hV
        _ = Bc * (1 / (1 - δ)) * glauberForm p X f := by ring
        _ ≤ Bc * Real.exp (A * (Real.log p / (p * Real.log X))) * glauberForm p X f :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hBc)
              (glauberForm_nonneg _ _ _)
        _ = K * Real.exp (Ψ p X) * glauberForm p X f := by rw [hBK]
    · -- `Q` is not prime: pass to `Q + 1`
      have hR : roughInterval (Q + 1) X = roughInterval Q X := roughInterval_succ_of_not_prime hQ X
      have hP : (Icc (Q + 1) X).filter Nat.Prime = (Icc Q X).filter Nat.Prime := by
        ext q
        simp only [mem_filter, mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          rcases h1.lt_or_eq with h | h
          · exact ⟨⟨h, h2⟩, h3⟩
          · exact absurd (h ▸ h3) hQ
      have hS : S (Q + 1) = S Q := by
        simp only [S, primesBelow_succ_eq, if_neg hQ]
      have hih := ih (X + 1 - (Q + 1)) (by omega) (Q + 1) X le_rfl hX f
      have hG : glauberForm (Q + 1) X f = glauberForm Q X f := by
        rw [glauberForm, glauberForm, hP, hR]
      rw [harmonicVar, ← hR]
      calc wVar (roughInterval (Q + 1) X) (fun n => 1 / (n : ℝ)) f = harmonicVar (Q + 1) X f := rfl
        _ ≤ K * Real.exp (Ψ (Q + 1) X) * glauberForm (Q + 1) X f := hih
        _ = K * Real.exp (Ψ Q X) * glauberForm Q X f := by simp only [Ψ, hS, hG]
  refine ⟨K, hK, fun Q X f => ?_⟩
  by_cases hX : 2 ≤ X
  · have h := claim (X + 1 - Q) Q X le_rfl hX f
    have hlX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hΨ : Ψ Q X ≤ 0 := by
      simp only [Ψ]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hS0 Q]) hlX.le
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (glauberForm_nonneg _ _ _))
    calc K * Real.exp (Ψ Q X) ≤ K * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hΨ) hK.le
      _ = K := mul_one K
  · rw [harmonicVar_eq_zero_of_le_one fun K hK => by
      have := mem_roughInterval.mp hK; omega]
    exact mul_nonneg hK.le (glauberForm_nonneg _ _ _)

/-- **Tensorization of the harmonic measure on `[1, X]`.** -/
theorem exists_harmonicVar_le_glauberForm :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, ∀ f : ℕ → ℝ, harmonicVar 0 X f ≤ C * glauberForm 0 X f := by
  obtain ⟨C, hC, h⟩ := exists_harmonicVar_le_glauberForm_rough
  exact ⟨C, hC, fun X f => h 0 X f⟩

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
