import GaloisForLFunctions.HTGeometry.BorelWeil.PrincipalMinors

/-!
# Realization of dominant weights by Borel–Weil sections

Given a multiplicity vector `m : Fin N → ℕ`, the product of leading principal minors
`bwVector m g = ∏ j, (leadingMinor (j+1) g) ^ m j` is a section of the Borel–Weil line bundle
attached to the weight `weightOfMult m i = ∑_{j ≥ i} m j`, and it takes the value `1` at the
identity.  Since `weightOfMult` is exactly the parametrization of the antitone (dominant) weights
by their consecutive differences, this proves the **non-vanishing half of the Borel–Weil
theorem**: `H⁰(λ) ≠ 0` for every dominant `λ`.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.weightOfMult`
* `GaloisForLFunctions.HTGeometry.BorelWeil.multOfWeight`
* `GaloisForLFunctions.HTGeometry.BorelWeil.bwVector`

## Main results

* `bwVector_mem_bwSections` — the minor product is a section of weight `weightOfMult m`.
* `weightOfMult_multOfWeight` — every antitone weight is a `weightOfMult`.
* `bwSections_ne_bot_of_antitone` — Borel–Weil non-vanishing for dominant weights.
-/

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {N : ℕ} {k : Type*} [CommRing k]

/-- The dominant weight attached to a multiplicity vector: `weightOfMult m i = ∑_{j ≥ i} m j`. -/
def weightOfMult (m : Fin N → ℕ) (i : Fin N) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin N => i ≤ j), m j

theorem antitone_weightOfMult (m : Fin N → ℕ) : Antitone (weightOfMult m) := by
  intro i i' h
  refine Finset.sum_le_sum_of_subset ?_
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact le_trans h hj

/-- The product of powers of leading principal minors attached to a multiplicity vector. -/
def bwVector (m : Fin N → ℕ) (g : SpecialLinearGroup (Fin N) k) : k :=
  ∏ j : Fin N, (leadingMinor ((j : ℕ) + 1) g) ^ (m j)

@[simp] theorem bwVector_one (m : Fin N → ℕ) :
    bwVector m (1 : SpecialLinearGroup (Fin N) k) = 1 := by
  simp [bwVector]

theorem bwVector_mem_regularFun (m : Fin N → ℕ) :
    (bwVector m : SpecialLinearGroup (Fin N) k → k) ∈ regularFun (Fin N) k := by
  have : (bwVector m : SpecialLinearGroup (Fin N) k → k)
      = ∏ j : Fin N, (fun g : SpecialLinearGroup (Fin N) k => leadingMinor ((j : ℕ) + 1) g) ^ m j := by
    funext g
    simp [bwVector, Finset.prod_apply]
  rw [this]
  exact Subalgebra.prod_mem _ fun j _ =>
    Subalgebra.pow_mem _ (leadingMinor_mem_regularFun _) _

/-- **Borel semi-invariance of the minor product.** -/
theorem bwVector_mul_borel (m : Fin N → ℕ) (g : SpecialLinearGroup (Fin N) k)
    {b : SpecialLinearGroup (Fin N) k} (hb : b ∈ borel (Fin N) k) :
    bwVector m (g * b) = borelChar (weightOfMult m) b * bwVector m g := by
  classical
  have hstep : ∀ j : Fin N,
      (leadingMinor ((j : ℕ) + 1) (g * b)) ^ (m j)
        = (leadingMinor ((j : ℕ) + 1) g) ^ (m j)
          * (∏ i : Fin N, (if i ≤ j then (b : Matrix (Fin N) (Fin N) k) i i else 1)) ^ (m j) := by
    intro j
    rw [leadingMinor_mul_borel _ g hb, mul_pow]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : i ≤ j
    · rw [if_pos (by exact Nat.lt_succ_of_le (Fin.le_def.mp h)), if_pos h]
    · rw [if_neg (by
        intro hcon
        exact h (Fin.le_def.mpr (Nat.lt_succ_iff.mp hcon))), if_neg h]
  rw [bwVector, Finset.prod_congr rfl fun j _ => hstep j, Finset.prod_mul_distrib, mul_comm]
  congr 1
  · rw [borelChar]
    rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) =>
      (Finset.prod_pow (Finset.univ)
        (m j) (fun i : Fin N => (if i ≤ j then (b : Matrix (Fin N) (Fin N) k) i i else 1))).symm]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hpt : ∀ j : Fin N,
        (if i ≤ j then (b : Matrix (Fin N) (Fin N) k) i i else 1) ^ (m j)
          = if i ≤ j then ((b : Matrix (Fin N) (Fin N) k) i i) ^ (m j) else 1 := by
      intro j
      by_cases h : i ≤ j
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, one_pow]
    rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) => hpt j, ← Finset.prod_filter,
      Finset.prod_pow_eq_pow_sum, weightOfMult]

theorem bwVector_mem_bwSections (m : Fin N → ℕ) :
    (bwVector m : SpecialLinearGroup (Fin N) k → k) ∈ bwSections (weightOfMult m) :=
  ⟨bwVector_mem_regularFun m, fun g _ hb => bwVector_mul_borel m g hb⟩

/-- The multiplicity vector attached to a weight: the consecutive difference `λ i - λ (i+1)`
(with `λ` extended by zero past the last index). -/
def multOfWeight (lam : Fin N → ℕ) (j : Fin N) : ℕ :=
  lam j - (if h : (j : ℕ) + 1 < N then lam ⟨(j : ℕ) + 1, h⟩ else 0)

private theorem sum_Ico_tsub_antitone {a : ℕ → ℕ} (ha : Antitone a) :
    ∀ (i n : ℕ), i ≤ n → ∑ t ∈ Finset.Ico i n, (a t - a (t + 1)) = a i - a n := by
  intro i n
  induction n with
  | zero => intro h; simp [Nat.le_zero.mp h]
  | succ n ih =>
    intro h
    rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · have hin : i ≤ n := Nat.lt_succ_iff.mp hlt
      rw [Finset.sum_Ico_succ_top hin, ih hin]
      have h1 : a n ≤ a i := ha hin
      have h2 : a (n + 1) ≤ a n := ha (Nat.le_succ n)
      omega
    · have : i = n + 1 := le_antisymm h hge
      subst this
      simp

/-- Every antitone (dominant) weight is the weight of its own multiplicity vector. -/
theorem weightOfMult_multOfWeight {lam : Fin N → ℕ} (hlam : Antitone lam) :
    weightOfMult (multOfWeight lam) = lam := by
  classical
  set a : ℕ → ℕ := fun t => if h : t < N then lam ⟨t, h⟩ else 0 with ha_def
  have ha : Antitone a := by
    intro s t hst
    by_cases htN : t < N
    · have hsN : s < N := lt_of_le_of_lt hst htN
      simp only [ha_def, dif_pos htN, dif_pos hsN]
      exact hlam (Fin.mk_le_mk.mpr hst)
    · simp [ha_def, dif_neg htN]
  have hm : ∀ j : Fin N, multOfWeight lam j = a (j : ℕ) - a ((j : ℕ) + 1) := by
    intro j
    simp [multOfWeight, ha_def, dif_pos j.isLt]
  funext i
  have hstep : weightOfMult (multOfWeight lam) i
      = ∑ j ∈ Finset.univ.filter (fun j : Fin N => i ≤ j),
          (a (j : ℕ) - a ((j : ℕ) + 1)) :=
    Finset.sum_congr rfl fun j _ => hm j
  have hmap : (Finset.univ.filter (fun j : Fin N => i ≤ j)).map Fin.valEmbedding
      = Finset.Ico (i : ℕ) N := by
    ext t
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico,
      Fin.valEmbedding_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Fin.le_def.mp hj, j.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨t, h2⟩, Fin.le_def.mpr h1, rfl⟩
  have hcast : ∑ j ∈ Finset.univ.filter (fun j : Fin N => i ≤ j),
      (a (j : ℕ) - a ((j : ℕ) + 1)) = ∑ t ∈ Finset.Ico (i : ℕ) N, (a t - a (t + 1)) := by
    rw [← hmap, Finset.sum_map]
    rfl
  rw [hstep, hcast, sum_Ico_tsub_antitone ha (i : ℕ) N (le_of_lt i.isLt)]
  simp [ha_def, dif_pos i.isLt]

/-- **Borel–Weil non-vanishing.**  For every dominant (antitone) weight `lam` the space of
sections of the associated line bundle on the flag variety of `SL(N,k)` is nonzero. -/
theorem bwSections_ne_bot_of_antitone [Nontrivial k] {lam : Fin N → ℕ} (hlam : Antitone lam) :
    bwSections (k := k) lam ≠ ⊥ := by
  intro hbot
  have hmem : (bwVector (multOfWeight lam) : SpecialLinearGroup (Fin N) k → k)
      ∈ bwSections (k := k) lam := by
    have h := bwVector_mem_bwSections (k := k) (multOfWeight lam)
    rwa [weightOfMult_multOfWeight hlam] at h
  rw [hbot, Submodule.mem_bot] at hmem
  have := congrFun hmem (1 : SpecialLinearGroup (Fin N) k)
  rw [bwVector_one] at this
  exact one_ne_zero this

end GaloisForLFunctions.HTGeometry.BorelWeil
