import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Formal vector fields on a line: the order calculus of the Lie bracket

A formal vector field on a line is `f ∂` with `f` a formal power series, and

```text
[f ∂, g ∂] = (f g' − f' g) ∂ .
```

The whole classification of transitive Lie pseudogroups in one variable rests on one computation:
if `f` and `g` vanish to *different* orders `a ≠ b`, then their bracket vanishes to order exactly
`a + b − 1`, with leading coefficient `(b − a)` times the product of the two leading coefficients.
In characteristic zero the factor `b − a` never vanishes, which is what makes the order arithmetic
rigid.

This file sets up that calculus with an explicit order predicate — `coeff n f ≠ 0` and all earlier
coefficients zero — so no `ℕ∞` arithmetic is needed anywhere.
-/

open PowerSeries

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- The Lie bracket of two formal vector fields on a line, written on their coefficient series. -/
def vfBracket (f g : PowerSeries K) : PowerSeries K :=
  f * (d⁄dX K) g - (d⁄dX K) f * g

theorem vfBracket_antisymm (f g : PowerSeries K) : vfBracket f g = -vfBracket g f := by
  unfold vfBracket
  ring

theorem vfBracket_self (f : PowerSeries K) : vfBracket f f = 0 := by
  unfold vfBracket
  ring

/-- `f` vanishes to order exactly `n`. -/
def HasOrder (f : PowerSeries K) (n : ℕ) : Prop :=
  coeff n f ≠ 0 ∧ ∀ i < n, coeff i f = 0

theorem HasOrder.ne_zero {f : PowerSeries K} {n : ℕ} (h : HasOrder f n) : f ≠ 0 := by
  intro hf
  exact h.1 (by rw [hf]; simp)

theorem HasOrder.unique {f : PowerSeries K} {m n : ℕ} (hm : HasOrder f m) (hn : HasOrder f n) :
    m = n := by
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact hm.1 (hn.2 m hlt)
  · exact hn.1 (hm.2 n hgt)

/-- Below its order a series has vanishing coefficients — the derivative version. -/
theorem coeff_deriv_eq_zero_of_lt {g : PowerSeries K} {b : ℕ} (hg : HasOrder g b)
    {j : ℕ} (hj : j + 1 < b) : coeff j ((d⁄dX K) g) = 0 := by
  rw [coeff_derivative, hg.2 (j + 1) hj, zero_mul]

/-! ## The leading coefficient of a bracket -/

theorem coeff_mul_deriv_of_hasOrder {f g : PowerSeries K} {a b : ℕ}
    (hf : HasOrder f a) (hg : HasOrder g b) (h1 : 1 ≤ a + b) :
    coeff (a + b - 1) (f * (d⁄dX K) g) = (b : K) * (coeff a f * coeff b g) := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have ha : 0 < a := by omega
    · have hn : a + 0 - 1 = a - 1 := by omega
      rw [hn, coeff_mul]
      have hzero : ∀ p ∈ Finset.antidiagonal (a - 1),
          coeff p.1 f * coeff p.2 ((d⁄dX K) g) = 0 := by
        intro p hp
        rw [Finset.mem_antidiagonal] at hp
        have hp1 : p.1 < a := by omega
        rw [hf.2 p.1 hp1, zero_mul]
      rw [Finset.sum_eq_zero hzero]
      simp
  · have hmem : (a, b - 1) ∈ Finset.antidiagonal (a + b - 1) := by
      rw [Finset.mem_antidiagonal]
      omega
    rw [coeff_mul, Finset.sum_eq_single (a, b - 1)]
    · rw [coeff_derivative]
      have hb1 : b - 1 + 1 = b := by omega
      have hcast : ((b - 1 : ℕ) : K) + 1 = (b : K) := by
        rw [Nat.cast_sub hb]
        norm_num
      rw [hb1, hcast]
      ring
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      rcases lt_or_ge p.1 a with hlt | hge
      · rw [hf.2 p.1 hlt, zero_mul]
      · have hp2 : p.2 + 1 < b := by
          rcases lt_or_ge (p.2 + 1) b with h | h
          · exact h
          · exfalso
            have : p.1 = a ∧ p.2 = b - 1 := by omega
            exact hne (Prod.ext this.1 this.2)
        rw [coeff_deriv_eq_zero_of_lt hg hp2, mul_zero]
    · intro h
      exact absurd hmem h

theorem coeff_deriv_mul_of_hasOrder {f g : PowerSeries K} {a b : ℕ}
    (hf : HasOrder f a) (hg : HasOrder g b) (h1 : 1 ≤ a + b) :
    coeff (a + b - 1) ((d⁄dX K) f * g) = (a : K) * (coeff a f * coeff b g) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hb : 0 < b := by omega
    · have hn : 0 + b - 1 = b - 1 := by omega
      rw [hn, coeff_mul]
      have hzero : ∀ p ∈ Finset.antidiagonal (b - 1),
          coeff p.1 ((d⁄dX K) f) * coeff p.2 g = 0 := by
        intro p hp
        rw [Finset.mem_antidiagonal] at hp
        have hp2 : p.2 < b := by omega
        rw [hg.2 p.2 hp2, mul_zero]
      rw [Finset.sum_eq_zero hzero]
      simp
  · have hmem : (a - 1, b) ∈ Finset.antidiagonal (a + b - 1) := by
      rw [Finset.mem_antidiagonal]
      omega
    rw [coeff_mul, Finset.sum_eq_single (a - 1, b)]
    · rw [coeff_derivative]
      have ha1 : a - 1 + 1 = a := by omega
      have hcast : ((a - 1 : ℕ) : K) + 1 = (a : K) := by
        rw [Nat.cast_sub ha]
        norm_num
      rw [ha1, hcast]
      ring
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      rcases lt_or_ge p.2 b with hlt | hge
      · rw [hg.2 p.2 hlt, mul_zero]
      · have hp1 : p.1 + 1 < a := by
          rcases lt_or_ge (p.1 + 1) a with h | h
          · exact h
          · exfalso
            have : p.1 = a - 1 ∧ p.2 = b := by omega
            exact hne (Prod.ext this.1 this.2)
        rw [coeff_deriv_eq_zero_of_lt hf hp1, zero_mul]
    · intro h
      exact absurd hmem h

/-- **The leading coefficient of a bracket.** -/
theorem coeff_vfBracket_of_hasOrder {f g : PowerSeries K} {a b : ℕ}
    (hf : HasOrder f a) (hg : HasOrder g b) (h1 : 1 ≤ a + b) :
    coeff (a + b - 1) (vfBracket f g) = ((b : K) - a) * (coeff a f * coeff b g) := by
  unfold vfBracket
  rw [map_sub, coeff_mul_deriv_of_hasOrder hf hg h1, coeff_deriv_mul_of_hasOrder hf hg h1]
  ring

/-- Below `a + b − 1` the bracket vanishes. -/
theorem coeff_vfBracket_eq_zero_of_lt {f g : PowerSeries K} {a b : ℕ}
    (hf : HasOrder f a) (hg : HasOrder g b) {n : ℕ} (hn : n < a + b - 1) :
    coeff n (vfBracket f g) = 0 := by
  have hfg : coeff n (f * (d⁄dX K) g) = 0 := by
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rcases lt_or_ge p.1 a with hlt | hge
    · rw [hf.2 p.1 hlt, zero_mul]
    · have hp2 : p.2 + 1 < b := by omega
      rw [coeff_deriv_eq_zero_of_lt hg hp2, mul_zero]
  have hgf : coeff n ((d⁄dX K) f * g) = 0 := by
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rcases lt_or_ge p.2 b with hlt | hge
    · rw [hg.2 p.2 hlt, mul_zero]
    · have hp1 : p.1 + 1 < a := by omega
      rw [coeff_deriv_eq_zero_of_lt hf hp1, zero_mul]
  unfold vfBracket
  rw [map_sub, hfg, hgf, sub_zero]

/-- **The order of a bracket of fields of different orders.**  In characteristic zero the factor
`b − a` is nonzero, so no cancellation can occur. -/
theorem hasOrder_vfBracket [CharZero K] {f g : PowerSeries K} {a b : ℕ}
    (hf : HasOrder f a) (hg : HasOrder g b) (hab : a ≠ b) :
    HasOrder (vfBracket f g) (a + b - 1) := by
  refine ⟨?_, fun i hi => coeff_vfBracket_eq_zero_of_lt hf hg hi⟩
  rw [coeff_vfBracket_of_hasOrder hf hg (by omega)]
  have hne : ((b : K) - a) ≠ 0 := by
    intro h
    have hcast : (b : K) = (a : K) := sub_eq_zero.mp h
    exact hab (Nat.cast_injective hcast).symm
  exact mul_ne_zero hne (mul_ne_zero hf.1 hg.1)


/-! ## Order arithmetic inside a bracket-closed subspace -/

/-- A subspace of coefficient series closed under the vector-field bracket. -/
def IsVfSubalgebra (L : Submodule K (PowerSeries K)) : Prop :=
  ∀ f ∈ L, ∀ g ∈ L, vfBracket f g ∈ L

variable [CharZero K]

/-- Bracketing with an order-zero field lowers the order by one. -/
theorem exists_hasOrder_sub_one {L : Submodule K (PowerSeries K)} (hL : IsVfSubalgebra L)
    {f h : PowerSeries K} (hfL : f ∈ L) (hhL : h ∈ L)
    (hf : HasOrder f 0) {n : ℕ} (hh : HasOrder h n) (hn : 1 ≤ n) :
    ∃ w ∈ L, HasOrder w (n - 1) := by
  refine ⟨vfBracket f h, hL f hfL h hhL, ?_⟩
  have hne : (0 : ℕ) ≠ n := by omega
  have := hasOrder_vfBracket hf hh hne
  simpa using this

/-- Bracketing with an order-two field raises the order by one. -/
theorem exists_hasOrder_add_one {L : Submodule K (PowerSeries K)} (hL : IsVfSubalgebra L)
    {u h : PowerSeries K} (huL : u ∈ L) (hhL : h ∈ L)
    (hu : HasOrder u 2) {n : ℕ} (hh : HasOrder h n) (hn : 3 ≤ n) :
    ∃ w ∈ L, HasOrder w (n + 1) := by
  refine ⟨vfBracket u h, hL u huL h hhL, ?_⟩
  have hne : (2 : ℕ) ≠ n := by omega
  have := hasOrder_vfBracket hu hh hne
  have hval : 2 + n - 1 = n + 1 := by omega
  rwa [hval] at this

/-- From an order-zero field, every order below a realized one is realized. -/
theorem exists_hasOrder_of_le {L : Submodule K (PowerSeries K)} (hL : IsVfSubalgebra L)
    {f : PowerSeries K} (hfL : f ∈ L) (hf : HasOrder f 0) :
    ∀ (n : ℕ) (h : PowerSeries K), h ∈ L → HasOrder h n → ∀ k, k ≤ n →
      ∃ w ∈ L, HasOrder w k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hhL hh k hkn
    rcases eq_or_lt_of_le hkn with rfl | hlt
    · exact ⟨h, hhL, hh⟩
    · obtain ⟨v, hvL, hv⟩ := exists_hasOrder_sub_one hL hfL hhL hf hh (by omega)
      exact ih (n - 1) (by omega) v hvL hv k (by omega)

/-- **The order tower.**  A transitive bracket-closed subspace containing a field of order at least
three contains one of order `m + k` for every `k`. -/
theorem exists_hasOrder_add {L : Submodule K (PowerSeries K)} (hL : IsVfSubalgebra L)
    {f h : PowerSeries K} (hfL : f ∈ L) (hhL : h ∈ L)
    (hf : HasOrder f 0) {m : ℕ} (hh : HasOrder h m) (hm : 3 ≤ m) :
    ∀ k : ℕ, ∃ w ∈ L, HasOrder w (m + k) := by
  obtain ⟨u, huL, hu⟩ := exists_hasOrder_of_le hL hfL hf m h hhL hh 2 (by omega)
  intro k
  induction k with
  | zero => exact ⟨h, hhL, hh⟩
  | succ k ihk =>
    obtain ⟨w, hwL, hw⟩ := ihk
    obtain ⟨v, hvL, hv⟩ := exists_hasOrder_add_one hL huL hwL hu hw (by omega)
    have heq : m + k + 1 = m + (k + 1) := by omega
    rw [heq] at hv
    exact ⟨v, hvL, hv⟩

/-- **Unbounded orders from a single high one.** -/
theorem exists_hasOrder_ge {L : Submodule K (PowerSeries K)} (hL : IsVfSubalgebra L)
    {f h : PowerSeries K} (hfL : f ∈ L) (hhL : h ∈ L)
    (hf : HasOrder f 0) {m : ℕ} (hh : HasOrder h m) (hm : 3 ≤ m) :
    ∀ N : ℕ, ∃ w ∈ L, ∃ n, N ≤ n ∧ HasOrder w n := by
  intro N
  obtain ⟨w, hwL, hw⟩ := exists_hasOrder_add hL hfL hhL hf hh hm N
  exact ⟨w, hwL, m + N, by omega, hw⟩

/-! ## Distinct orders are independent -/

omit [CharZero K] in
/-- Fields with pairwise distinct orders are linearly independent. -/
theorem linearIndependent_of_hasOrder_injective {ι : Type*} {w : ι → PowerSeries K} {n : ι → ℕ}
    (hw : ∀ i, HasOrder (w i) (n i)) (hn : Function.Injective n) :
    LinearIndependent K w := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i₀ hi₀
  by_contra hc
  have hTne : (s.filter (fun i => c i ≠ 0)).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hc⟩⟩
  obtain ⟨j, hjT, hjmin⟩ := (s.filter (fun i => c i ≠ 0)).exists_min_image n hTne
  obtain ⟨hjs, hjc⟩ := Finset.mem_filter.mp hjT
  have hcoeff : ∑ i ∈ s, c i * coeff (n j) (w i) = 0 := by
    have h := congrArg (fun x : PowerSeries K => coeff (n j) x) hsum
    simpa [map_sum, smul_eq_mul] using h
  have hterm : ∀ i ∈ s, i ≠ j → c i * coeff (n j) (w i) = 0 := by
    intro i his hij
    by_cases hci : c i = 0
    · rw [hci, zero_mul]
    · have hiT : i ∈ s.filter (fun i => c i ≠ 0) := Finset.mem_filter.mpr ⟨his, hci⟩
      have hle : n j ≤ n i := hjmin i hiT
      have hne : n j ≠ n i := fun h => hij (hn h).symm
      rw [(hw i).2 (n j) (lt_of_le_of_ne hle hne), mul_zero]
  rw [Finset.sum_eq_single_of_mem j hjs hterm] at hcoeff
  exact (mul_ne_zero hjc (hw j).1) hcoeff


/-! ## The rank bound -/

/-- **The Lie--Cartan rank bound in one variable.**  A finite-dimensional bracket-closed subspace of
formal vector fields that is transitive — it contains a field with nonvanishing constant term —
contains no field vanishing to order three or more.  Its orders therefore lie in `{0, 1, 2}`, so its
dimension is at most three: this is the algebraic core of the classification of proper transitive
one-dimensional pseudogroups into the tensor, affine and projective cases. -/
theorem hasOrder_le_two_of_finiteDimensional {L : Submodule K (PowerSeries K)}
    [FiniteDimensional K L] (hL : IsVfSubalgebra L)
    {f : PowerSeries K} (hfL : f ∈ L) (hf : HasOrder f 0)
    {h : PowerSeries K} {m : ℕ} (hhL : h ∈ L) (hh : HasOrder h m) :
    m ≤ 2 := by
  classical
  by_contra hmc
  have hm : 3 ≤ m := by omega
  have hstep := exists_hasOrder_add hL hfL hhL hf hh hm
  choose w hwL hwO using hstep
  have hindepW : LinearIndependent K w :=
    linearIndependent_of_hasOrder_injective hwO (fun i j hij => by omega)
  set v : ℕ → L := fun k => ⟨w k, hwL k⟩ with hv
  have hindepV : LinearIndependent K v := by
    refine LinearIndependent.of_comp L.subtype ?_
    exact hindepW
  have hfin : LinearIndependent K (v ∘ (fun i : Fin (Module.finrank K L + 1) => (i : ℕ))) :=
    hindepV.comp _ Fin.val_injective
  have hcard := LinearIndependent.fintype_card_le_finrank hfin
  simp only [Fintype.card_fin] at hcard
  omega


omit [CharZero K] in
/-- Every nonzero power series vanishes to a definite order. -/
theorem exists_hasOrder_of_ne_zero {f : PowerSeries K} (hf : f ≠ 0) : ∃ n, HasOrder f n := by
  classical
  have hex : ∃ n, coeff n f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (PowerSeries.ext fun n => by rw [hcon n]; simp)
  refine ⟨Nat.find hex, Nat.find_spec hex, fun i hi => ?_⟩
  exact not_not.mp (Nat.find_min hex hi)

/-- The first three coefficients, as a linear map. -/
def lowCoeffs : PowerSeries K →ₗ[K] (Fin 3 → K) where
  toFun f := fun i => coeff (i : ℕ) f
  map_add' f g := by
    funext i
    simp
  map_smul' c f := by
    funext i
    simp

/-- **Rank at most three.**  A finite-dimensional transitive bracket-closed subspace of formal
vector fields has dimension at most three: every element is determined by its first three
coefficients, because no element vanishes to order three. -/
theorem finrank_le_three {L : Submodule K (PowerSeries K)}
    [FiniteDimensional K L] (hL : IsVfSubalgebra L)
    {f : PowerSeries K} (hfL : f ∈ L) (hf : HasOrder f 0) :
    Module.finrank K L ≤ 3 := by
  classical
  have hinj : Function.Injective (lowCoeffs.comp L.subtype) := by
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    by_contra hxne
    have hxv : (x : PowerSeries K) ≠ 0 := by
      intro h
      exact hxne (Subtype.ext h)
    obtain ⟨n, hn⟩ := exists_hasOrder_of_ne_zero hxv
    have hle : n ≤ 2 := hasOrder_le_two_of_finiteDimensional hL hfL hf x.2 hn
    have hcoeff : coeff n (x : PowerSeries K) = 0 := by
      have := congrFun hx ⟨n, by omega⟩
      simpa [lowCoeffs] using this
    exact hn.1 hcoeff
  have h := LinearMap.finrank_le_finrank_of_injective (f := lowCoeffs.comp L.subtype) hinj
  simpa [Module.finrank_pi] using h

end GaloisForLFunctions.HTGeometry

end
