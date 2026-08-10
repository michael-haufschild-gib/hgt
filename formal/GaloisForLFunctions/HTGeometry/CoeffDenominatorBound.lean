import GaloisForLFunctions.HTGeometry.EisensteinRecursion

/-!
# Geometrically bounded denominators

The conclusion of Eisenstein's theorem — that the coefficients of an algebraic power series have
denominators growing at most geometrically — is the statement that `q ^ (κ N) · f_N` lies in the
base ring for every `N`, for some fixed `q` and `κ`.  The induction that proves it needs a slightly
finer bookkeeping: a *gain*, recording that the rescaled coefficient is not merely in the base ring
but divisible there by a further power `q ^ β`.

That is `CoeffBnd A q κ β`.  Its two structural properties are what the induction runs on: the
bound is additive in `f`, and multiplying two bounded series *adds the gains*.  The gain is what
pays for the one factor of `q` lost at each step of the recursion — a product of two bounded factors
gains `2β` and loses `1`, so it closes as soon as `β ≥ 1`, while a single factor gains only `β` and
must be paid for by the strict drop of the index instead.

No completeness, no valuation, no Noetherian hypothesis: only a subring of a field and a chosen
element of it.
-/

namespace GaloisForLFunctions.HTGeometry

open PowerSeries

variable {K : Type*} [Field K]

/-! ## Divisibility by a power inside a subring -/

/-- `x` is `q ^ β` times an element of `A`. -/
def IsPowMul (A : Subring K) (q : K) (β : ℕ) (x : K) : Prop := ∃ a ∈ A, x = q ^ β * a

theorem isPowMul_zero {A : Subring K} {q : K} {β : ℕ} : IsPowMul A q β 0 :=
  ⟨0, A.zero_mem, by rw [mul_zero]⟩

theorem IsPowMul.add {A : Subring K} {q : K} {β : ℕ} {x y : K}
    (hx : IsPowMul A q β x) (hy : IsPowMul A q β y) : IsPowMul A q β (x + y) := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  exact ⟨a + b, A.add_mem ha hb, by rw [hxa, hyb]; ring⟩

theorem IsPowMul.sum {A : Subring K} {q : K} {β : ℕ} {ι : Type*} (s : Finset ι) (g : ι → K)
    (hg : ∀ i ∈ s, IsPowMul A q β (g i)) : IsPowMul A q β (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isPowMul_zero
  | insert j t hjt ih =>
      rw [Finset.sum_insert hjt]
      exact (hg j (Finset.mem_insert_self _ _)).add
        (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem IsPowMul.mul {A : Subring K} {q : K} {β γ : ℕ} {x y : K}
    (hx : IsPowMul A q β x) (hy : IsPowMul A q γ y) : IsPowMul A q (β + γ) (x * y) := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  refine ⟨a * b, A.mul_mem ha hb, ?_⟩
  rw [hxa, hyb, pow_add]
  ring

theorem IsPowMul.mul_left {A : Subring K} {q : K} {β : ℕ} {a x : K} (ha : a ∈ A)
    (hx : IsPowMul A q β x) : IsPowMul A q β (a * x) := by
  obtain ⟨b, hb, hxb⟩ := hx
  exact ⟨a * b, A.mul_mem ha hb, by rw [hxb]; ring⟩

theorem isPowMul_zero_iff_mem {A : Subring K} {q : K} {x : K} :
    IsPowMul A q 0 x ↔ x ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [pow_zero, one_mul]
    exact ha
  · intro hx
    exact ⟨x, hx, by rw [pow_zero, one_mul]⟩

/-- Weakening the gain, at the cost of `q` lying in the ring. -/
theorem IsPowMul.mono {A : Subring K} {q : K} (hq : q ∈ A) {β γ : ℕ} (hβγ : γ ≤ β) {x : K}
    (hx : IsPowMul A q β x) : IsPowMul A q γ x := by
  obtain ⟨a, ha, hxa⟩ := hx
  refine ⟨q ^ (β - γ) * a, A.mul_mem (A.pow_mem hq _) ha, ?_⟩
  rw [hxa, ← mul_assoc, ← pow_add]
  congr 2
  omega

/-! ## Geometrically bounded coefficients -/

/-- The coefficients of `f` have denominators bounded by `q ^ (κ N)`, with a gain of `q ^ β`. -/
def CoeffBnd (A : Subring K) (q : K) (κ β : ℕ) (f : PowerSeries K) : Prop :=
  ∀ N, IsPowMul A q β (q ^ (κ * N) * PowerSeries.coeff N f)

theorem CoeffBnd.add {A : Subring K} {q : K} {κ β : ℕ} {f g : PowerSeries K}
    (hf : CoeffBnd A q κ β f) (hg : CoeffBnd A q κ β g) : CoeffBnd A q κ β (f + g) := by
  intro N
  rw [map_add, mul_add]
  exact (hf N).add (hg N)

theorem CoeffBnd.neg {A : Subring K} {q : K} {κ β : ℕ} {f : PowerSeries K}
    (hf : CoeffBnd A q κ β f) : CoeffBnd A q κ β (-f) := by
  intro N
  obtain ⟨a, ha, hae⟩ := hf N
  refine ⟨-a, A.neg_mem ha, ?_⟩
  rw [map_neg, mul_neg, hae]
  ring

/-- **Multiplying bounded series adds the gains.** -/
theorem CoeffBnd.mul {A : Subring K} {q : K} {κ β γ : ℕ} {f g : PowerSeries K}
    (hf : CoeffBnd A q κ β f) (hg : CoeffBnd A q κ γ g) : CoeffBnd A q κ (β + γ) (f * g) := by
  intro N
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  refine IsPowMul.sum _ _ fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hsplit : q ^ (κ * N) * (PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g)
      = (q ^ (κ * p.1) * PowerSeries.coeff p.1 f) * (q ^ (κ * p.2) * PowerSeries.coeff p.2 g) := by
    rw [← hp, Nat.mul_add, pow_add]
    ring
  rw [hsplit]
  exact (hf p.1).mul (hg p.2)

theorem CoeffBnd.pow {A : Subring K} {q : K} {κ β : ℕ} {f : PowerSeries K}
    (hf : CoeffBnd A q κ β f) (i : ℕ) : CoeffBnd A q κ (i * β) (f ^ i) := by
  induction i with
  | zero =>
      intro N
      rw [pow_zero, Nat.zero_mul, isPowMul_zero_iff_mem]
      by_cases hN : N = 0
      · subst hN
        rw [Nat.mul_zero, pow_zero, one_mul, PowerSeries.coeff_one, if_pos rfl]
        exact A.one_mem
      · rw [PowerSeries.coeff_one, if_neg hN, mul_zero]
        exact A.zero_mem
  | succ i ih =>
      have := ih.mul hf
      rw [pow_succ]
      have hrw : i * β + β = (i + 1) * β := by ring
      rwa [hrw] at this

/-- Coefficients in the base ring give the trivial bound. -/
theorem coeffBnd_of_coeff_mem {A : Subring K} {q : K} (hq : q ∈ A) (κ : ℕ) {f : PowerSeries K}
    (hf : ∀ N, PowerSeries.coeff N f ∈ A) : CoeffBnd A q κ 0 f := by
  intro N
  rw [isPowMul_zero_iff_mem]
  exact A.mul_mem (A.pow_mem hq _) (hf N)

/-- Truncation preserves the bound. -/
theorem CoeffBnd.truncPS {A : Subring K} {q : K} {κ β : ℕ} {f : PowerSeries K}
    (hf : CoeffBnd A q κ β f) (n : ℕ) : CoeffBnd A q κ β (truncPS n f) := by
  intro N
  rw [coeff_truncPS]
  by_cases hN : N < n
  · rw [if_pos hN]
    exact hf N
  · rw [if_neg hN, mul_zero]
    exact isPowMul_zero

/-- Weakening the gain. -/
theorem CoeffBnd.mono {A : Subring K} {q : K} (hq : q ∈ A) {κ β γ : ℕ} (hβγ : γ ≤ β)
    {f : PowerSeries K} (hf : CoeffBnd A q κ β f) : CoeffBnd A q κ γ f :=
  fun N => (hf N).mono hq hβγ

theorem CoeffBnd.sum {A : Subring K} {q : K} {κ β : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → PowerSeries K) (hg : ∀ i ∈ s, CoeffBnd A q κ β (g i)) :
    CoeffBnd A q κ β (∑ i ∈ s, g i) := by
  intro N
  rw [map_sum, Finset.mul_sum]
  exact IsPowMul.sum _ _ fun i hi => hg i hi N

/-- **Evaluating a polynomial with bounded coefficients at a bounded series.** -/
theorem CoeffBnd.eval {A : Subring K} {q : K} (hq : q ∈ A) {κ β : ℕ} {P : Polynomial (PowerSeries K)}
    (hP : ∀ i, CoeffBnd A q κ 0 (P.coeff i)) {w : PowerSeries K} (hw : CoeffBnd A q κ β w) :
    CoeffBnd A q κ 0 (P.eval w) := by
  rw [Polynomial.eval_eq_sum_range]
  refine CoeffBnd.sum _ _ fun i _ => ?_
  exact ((hP i).mul (hw.pow i)).mono hq (Nat.zero_le _)

/-! ## The case of no denominators at all -/

/-- With exponent and gain both zero the bound says exactly that all coefficients lie in `A`. -/
theorem coeffBnd_zero_zero_iff {A : Subring K} {q : K} {f : PowerSeries K} :
    CoeffBnd A q 0 0 f ↔ ∀ N, PowerSeries.coeff N f ∈ A := by
  constructor
  · intro h N
    have := h N
    rw [Nat.zero_mul, pow_zero, one_mul, isPowMul_zero_iff_mem] at this
    exact this
  · intro h N
    rw [Nat.zero_mul, pow_zero, one_mul, isPowMul_zero_iff_mem]
    exact h N

theorem coeffMem_shiftPow {A : Subring K} {f : PowerSeries K}
    (hf : ∀ N, PowerSeries.coeff N f ∈ A) (k : ℕ) :
    ∀ N, PowerSeries.coeff N (shiftPow k f) ∈ A := by
  intro N
  rw [coeff_shiftPow]
  exact hf _

theorem coeffMem_X_pow_mul {A : Subring K} {f : PowerSeries K}
    (hf : ∀ N, PowerSeries.coeff N f ∈ A) (k : ℕ) :
    ∀ N, PowerSeries.coeff N ((PowerSeries.X : PowerSeries K) ^ k * f) ∈ A := by
  intro N
  rcases Nat.lt_or_ge N k with hN | hN
  · have hdvd : (PowerSeries.X : PowerSeries K) ^ k ∣
        (PowerSeries.X : PowerSeries K) ^ k * f := ⟨_, rfl⟩
    rw [PowerSeries.X_pow_dvd_iff] at hdvd
    rw [hdvd N hN]
    exact A.zero_mem
  · obtain ⟨d, hd⟩ : ∃ d, N = d + k := ⟨N - k, by omega⟩
    subst hd
    rw [PowerSeries.coeff_X_pow_mul]
    exact hf d

/-- The Hasse derivative of a polynomial with `A`-coefficients again has `A`-coefficients. -/
theorem coeffMem_hasseDeriv {A : Subring K} {F : Polynomial (PowerSeries K)}
    (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A) (k : ℕ) :
    ∀ i N, PowerSeries.coeff N ((Polynomial.hasseDeriv k F).coeff i) ∈ A := by
  intro i N
  rw [Polynomial.hasseDeriv_coeff, ← nsmul_eq_mul, map_nsmul]
  exact nsmul_mem (hF (i + k) N) _

end GaloisForLFunctions.HTGeometry
