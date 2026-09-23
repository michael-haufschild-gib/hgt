import Mathlib

/-!
# The off-diagonal through the difference multiset: where additive energy enters

Every moment-method large-values bound estimates the off-diagonal

```text
∑_{r ≠ s} f( t_r − t_s )
```

by *worst case times count*: `≤ (sup f) · R²`, or by a row-sum bound as in
`SeparatedOffDiagonalBound`.  Both discard the fact that the differences `t_r − t_s` are not
arbitrary — they form a multiset whose repetition structure is exactly the additive energy of the
sampling set.

Collecting equal differences first and applying Cauchy–Schwarz to the resulting sum over *distinct*
differences replaces `sup × count` by

```text
√(additive energy) · ‖f‖_{ℓ²(differences)} ,
```

which is smaller precisely when the sampling set is additively unstructured.  This is the step that
leaves the `min(power, meanValue)` family: the bound now depends on the *structure* of the large-value
set, not only on its cardinality.

The dichotomy that follows — either the energy is small, and this bound wins, or it is large, and the
set is close to an arithmetic progression and can be handled directly — is the shape of the modern
structural large-values arguments.  This module proves the inequality; the dichotomy is downstream.
-/

open Finset

namespace GaloisForLFunctions

variable {ι D : Type*} [Fintype ι] [DecidableEq D]

/-- The multiplicity of a difference value in the difference multiset of the sampling set. -/
noncomputable def diffMult (d : ι → ι → D) (x : D) : ℕ :=
  ((univ : Finset (ι × ι)).filter fun p => d p.1 p.2 = x).card

/-- **Collecting equal differences.**  A sum over pairs is a sum over distinct difference values,
weighted by multiplicity. -/
theorem sum_pairs_eq_sum_diff (d : ι → ι → D) (f : D → ℝ) (S : Finset D)
    (hmem : ∀ p : ι × ι, d p.1 p.2 ∈ S) :
    ∑ p : ι × ι, f (d p.1 p.2) = ∑ x ∈ S, (diffMult d x : ℝ) * f x := by
  classical
  have hfib : ∑ p : ι × ι, f (d p.1 p.2)
      = ∑ x ∈ S, ∑ p ∈ (univ : Finset (ι × ι)).filter fun p => d p.1 p.2 = x,
          f (d p.1 p.2) :=
    (Finset.sum_fiberwise_of_maps_to (fun p _ => hmem p) _).symm
  rw [hfib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hconst : ∀ p ∈ (univ : Finset (ι × ι)).filter fun p => d p.1 p.2 = x,
      f (d p.1 p.2) = f x := by
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, diffMult, nsmul_eq_mul]

/-- **The difference-energy bound.**  The off-diagonal sum is at most the square root of the additive
energy times the `ℓ²` norm of the kernel over distinct differences — replacing `sup × count` by a
bound that sees the structure of the sampling set. -/
theorem sum_pairs_le_sqrt_energy (d : ι → ι → D) (f : D → ℝ) (S : Finset D)
    (hmem : ∀ p : ι × ι, d p.1 p.2 ∈ S) :
    ∑ p : ι × ι, f (d p.1 p.2)
      ≤ Real.sqrt (∑ x ∈ S, (diffMult d x : ℝ) ^ (2 : ℕ)) * Real.sqrt (∑ x ∈ S, f x ^ (2 : ℕ)) := by
  classical
  rw [sum_pairs_eq_sum_diff d f S hmem]
  have hcs : (∑ x ∈ S, (diffMult d x : ℝ) * f x) ^ (2 : ℕ)
      ≤ (∑ x ∈ S, (diffMult d x : ℝ) ^ (2 : ℕ)) * ∑ x ∈ S, f x ^ (2 : ℕ) :=
    Finset.sum_mul_sq_le_sq_mul_sq S (fun x => (diffMult d x : ℝ)) f
  have hE : 0 ≤ ∑ x ∈ S, (diffMult d x : ℝ) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hF : 0 ≤ ∑ x ∈ S, f x ^ (2 : ℕ) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hprod : Real.sqrt (∑ x ∈ S, (diffMult d x : ℝ) ^ (2 : ℕ)) * Real.sqrt (∑ x ∈ S, f x ^ (2 : ℕ))
      = Real.sqrt ((∑ x ∈ S, (diffMult d x : ℝ) ^ (2 : ℕ)) * ∑ x ∈ S, f x ^ (2 : ℕ)) :=
    (Real.sqrt_mul hE _).symm
  rw [hprod]
  have h1 : Real.sqrt ((∑ x ∈ S, (diffMult d x : ℝ) * f x) ^ (2 : ℕ))
      ≤ Real.sqrt ((∑ x ∈ S, (diffMult d x : ℝ) ^ (2 : ℕ)) * ∑ x ∈ S, f x ^ (2 : ℕ)) :=
    Real.sqrt_le_sqrt hcs
  rw [Real.sqrt_sq_eq_abs] at h1
  exact le_trans (le_abs_self _) h1

/-- The total multiplicity is the number of pairs: `∑_x m(x) = |ι|²`.  So the energy
`∑_x m(x)²` is at least `|ι|⁴ / |S|` by Cauchy–Schwarz, and equality is the maximally structured
case — an arithmetic progression. -/
theorem sum_diffMult (d : ι → ι → D) (S : Finset D)
    (hmem : ∀ p : ι × ι, d p.1 p.2 ∈ S) :
    ∑ x ∈ S, (diffMult d x : ℝ) = (Fintype.card ι : ℝ) ^ (2 : ℕ) := by
  classical
  have h := sum_pairs_eq_sum_diff d (fun _ => (1 : ℝ)) S hmem
  simp only [mul_one] at h
  rw [← h]
  simp [Fintype.card_prod, sq]


/-! ### The structured branch: an arithmetic progression has exactly computable multiplicities

The dichotomy's other side.  When the sampling set is an arithmetic progression the difference
multiset is completely explicit — the multiplicity of the `k`-th difference is `R − k` — so the
off-diagonal is a single one-dimensional sum with triangular weights, and no estimate is needed.
This is why the structured branch is tractable: the Gram becomes Toeplitz. -/

/-- **Arithmetic-progression multiplicities.**  Among pairs from `range R`, exactly `R − k` have
first coordinate exceeding the second by `k`. -/
theorem card_pairs_diff_eq (R k : ℕ) (hk : k ≤ R) :
    ((Finset.range R ×ˢ Finset.range R).filter fun p => p.1 = p.2 + k).card = R - k := by
  classical
  have himg : (Finset.range R ×ˢ Finset.range R).filter (fun p => p.1 = p.2 + k)
      = (Finset.range (R - k)).image fun s => (s + k, s) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, heq⟩
      refine ⟨p.2, by omega, ?_⟩
      rw [← heq]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨by omega, by omega⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.snd hab),
    Finset.card_range]

/-- The triangular weight is positive exactly below the length, and vanishes at the length: the
difference multiset of an `R`-term progression is supported on `|k| < R`. -/
theorem card_pairs_diff_eq_zero (R : ℕ) :
    ((Finset.range R ×ˢ Finset.range R).filter fun p => p.1 = p.2 + R).card = 0 := by
  rw [card_pairs_diff_eq R R (le_refl R)]
  omega

/-- **Toeplitz structure.**  On an arithmetic progression the difference depends only on the index
difference, so the sampling Gram is constant along diagonals. -/
theorem ap_diff (a d : ℝ) (r s : ℕ) :
    (a + (r : ℝ) * d) - (a + (s : ℝ) * d) = ((r : ℝ) - s) * d := by ring



/-! ### From the unweighted energy bound to the large-values setting

The energy bound is unweighted, while a large-values argument carries weights `|b_r|`.  In the
large-values setting the weights are essentially constant — every sampled value has modulus at least
`V`, and a dyadic split makes them comparable — so bounding them above by `B` transfers the energy
bound directly.  No transference theorem is needed for this half of the dichotomy. -/

omit [DecidableEq D] in
/-- **Constant-weight transfer.**  Bounded weights reduce the weighted pair sum to the unweighted
one. -/
theorem weighted_pairs_le_of_bounded {b : ι → ℝ} {B : ℝ} (d : ι → ι → D) (f : D → ℝ)
    (hb : ∀ r, |b r| ≤ B) (hB : 0 ≤ B) (hf : ∀ x, 0 ≤ f x) :
    ∑ p : ι × ι, |b p.1| * |b p.2| * f (d p.1 p.2)
      ≤ B ^ (2 : ℕ) * ∑ p : ι × ι, f (d p.1 p.2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have h1 : |b p.1| * |b p.2| ≤ B ^ (2 : ℕ) := by
    have := mul_le_mul (hb p.1) (hb p.2) (abs_nonneg _) hB
    nlinarith [this]
  exact mul_le_mul_of_nonneg_right h1 (hf _)

/-- **The trivial multiplicity bound.**  If the first coordinate and the difference determine the
second, each difference occurs at most `|ι|` times. -/
theorem diffMult_le_card (d : ι → ι → D) (x : D)
    (hdet : ∀ r s s' : ι, d r s = x → d r s' = x → s = s') :
    diffMult d x ≤ Fintype.card ι := by
  classical
  unfold diffMult
  have hinj : Set.InjOn (Prod.fst : ι × ι → ι)
      ((((univ : Finset (ι × ι)).filter fun p => d p.1 p.2 = x) : Finset (ι × ι)) :
        Set (ι × ι)) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    have h2 : p.2 = q.2 := hdet p.1 p.2 q.2 hp.2 (by rw [hpq]; exact hq.2)
    exact Prod.ext hpq h2
  calc ((univ : Finset (ι × ι)).filter fun p => d p.1 p.2 = x).card
      = (((univ : Finset (ι × ι)).filter fun p => d p.1 p.2 = x).image Prod.fst).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (univ : Finset ι).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card ι := Finset.card_univ

/-- **The trivial energy bound.**  With multiplicities at most `R` and total mass `R²`, the additive
energy is at most `R³` — so `√E ≤ R^{3/2}`, against the `R²` that a `sup × count` bound pays. -/
theorem energy_le_cube (d : ι → ι → D) (S : Finset D)
    (hmem : ∀ p : ι × ι, d p.1 p.2 ∈ S)
    (hdet : ∀ x : D, ∀ r s s' : ι, d r s = x → d r s' = x → s = s') :
    ∑ x ∈ S, (diffMult d x : ℝ) ^ (2 : ℕ)
      ≤ (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) ^ (2 : ℕ) := by
  classical
  have hle : ∀ x ∈ S, (diffMult d x : ℝ) ^ (2 : ℕ)
      ≤ (Fintype.card ι : ℝ) * (diffMult d x : ℝ) := by
    intro x _
    have h := diffMult_le_card d x (hdet x)
    have hcast : (diffMult d x : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast h
    nlinarith [Nat.cast_nonneg (α := ℝ) (diffMult d x)]
  calc ∑ x ∈ S, (diffMult d x : ℝ) ^ (2 : ℕ)
      ≤ ∑ x ∈ S, (Fintype.card ι : ℝ) * (diffMult d x : ℝ) := Finset.sum_le_sum hle
    _ = (Fintype.card ι : ℝ) * ∑ x ∈ S, (diffMult d x : ℝ) := by rw [Finset.mul_sum]
    _ = (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) ^ (2 : ℕ) := by
        rw [sum_diffMult d S hmem]



/-! ### The two branches in comparable form

Collecting by difference gives two routes, and they are the `ℓ¹` and `ℓ²` treatments of the same
sum:

```text
ℓ¹ route :  ∑_{r,s} f(t_r − t_s)  ≤  R · ‖f‖_{ℓ¹(differences)}       (multiplicity ≤ R)
ℓ² route :  ∑_{r,s} f(t_r − t_s)  ≤  √E · ‖f‖_{ℓ²(differences)}      (Cauchy–Schwarz)
```

For an arithmetic progression `E` is maximal (`≈ R³`) and the `ℓ¹` route wins; for an additively
unstructured set `E` is minimal (`≈ R²`) and the `ℓ²` route wins by a power of `R`.  Taking the
minimum is the structural estimate, and it is strictly better than either alone. -/

/-- **The `ℓ¹` route.**  Multiplicities bounded by the count give the `ℓ¹` bound, which is the sharp
one for maximally structured sampling sets. -/
theorem sum_pairs_le_card_mul_l1 (d : ι → ι → D) (f : D → ℝ) (S : Finset D)
    (hmem : ∀ p : ι × ι, d p.1 p.2 ∈ S) (hf : ∀ x, 0 ≤ f x)
    (hdet : ∀ x : D, ∀ r s s' : ι, d r s = x → d r s' = x → s = s') :
    ∑ p : ι × ι, f (d p.1 p.2) ≤ (Fintype.card ι : ℝ) * ∑ x ∈ S, f x := by
  classical
  rw [sum_pairs_eq_sum_diff d f S hmem, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have h := diffMult_le_card d x (hdet x)
  have hcast : (diffMult d x : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_right hcast (hf x)

/-- **The structural estimate.**  The pair sum is at most the minimum of the `ℓ¹` and `ℓ²` routes;
neither dominates, and which wins is exactly whether the sampling set is additively structured. -/
theorem sum_pairs_le_min (d : ι → ι → D) (f : D → ℝ) (S : Finset D)
    (hmem : ∀ p : ι × ι, d p.1 p.2 ∈ S) (hf : ∀ x, 0 ≤ f x)
    (hdet : ∀ x : D, ∀ r s s' : ι, d r s = x → d r s' = x → s = s') :
    ∑ p : ι × ι, f (d p.1 p.2)
      ≤ min ((Fintype.card ι : ℝ) * ∑ x ∈ S, f x)
          (Real.sqrt (∑ x ∈ S, (diffMult d x : ℝ) ^ (2 : ℕ)) * Real.sqrt (∑ x ∈ S, f x ^ (2 : ℕ))) :=
  le_min (sum_pairs_le_card_mul_l1 d f S hmem hf hdet)
    (sum_pairs_le_sqrt_energy d f S hmem)


end GaloisForLFunctions
