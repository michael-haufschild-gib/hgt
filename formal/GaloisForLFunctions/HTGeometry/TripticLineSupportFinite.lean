import GaloisForLFunctions.HTGeometry.TripticTransverseCoefficient
import GaloisForLFunctions.HTGeometry.TripticIndexBound
import GaloisForLFunctions.HTGeometry.FinsumIntSplit

/-!
# Only finitely many lines carry a nonzero transverse coefficient

A nonzero row coefficient at `w` forces a pole of the `τ`-boundary function both forward and
backward along the `τ`-ray through `w`: forward because the coefficient is the forward sum, backward
because the total sum along the ray vanishes, so the forward sum is minus the backward one.

The two poles reduce, modulo the lattice `ℤ + ℤσ`, to a finite list of representatives, and the
number of `τ`-steps between two such representatives is bounded — that is the shift-index finiteness.
So the forward index is bounded, and `w` itself lies in a finite list of classes modulo `ℤ + ℤσ`.

* `rowCoeff_eq_backward_sum` — the second formula for the row coefficient;
* `exists_finset_rowCoeff_classes`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

noncomputable section

variable {F : ℂ → ℂ} {τ σ : ℂ}

/-- **The row coefficient is also the backward sum.**  The total transverse mass vanishes, so the
forward sum is minus the backward one. -/
theorem rowCoeff_eq_backward_sum {ℓ : ℤ} {w : ℂ}
    (hfin : {n : ℤ | laurentCoeff (fun z => F (z + τ) - F z) (w + (n : ℂ) * τ) ℓ ≠ 0}.Finite)
    (hzero : ∑ᶠ n : ℤ, laurentCoeff (fun z => F (z + τ) - F z) (w + (n : ℂ) * τ) ℓ = 0) :
    rowCoeff F τ ℓ w
      = ∑ᶠ j : ℕ, laurentCoeff (fun z => F (z + τ) - F z)
          (w + ((-((j : ℤ) + 1) : ℤ) : ℂ) * τ) ℓ := by
  set A : ℤ → ℂ := fun n => laurentCoeff (fun z => F (z + τ) - F z) (w + (n : ℂ) * τ) ℓ with hA
  have hsplit := finsum_int_split (A := A) hfin
  rw [hzero] at hsplit
  rw [rowCoeff]
  have hforward : (∑ᶠ k : ℕ, laurentCoeff (fun z => F (z + τ) - F z) (w + ((k : ℤ) : ℂ) * τ) ℓ)
      = ∑ᶠ k : ℕ, A (k : ℤ) := rfl
  have hbackward : (∑ᶠ j : ℕ, laurentCoeff (fun z => F (z + τ) - F z)
      (w + ((-((j : ℤ) + 1) : ℤ) : ℂ) * τ) ℓ) = ∑ᶠ j : ℕ, A (-((j : ℤ) + 1)) := rfl
  rw [hforward, hbackward]
  linear_combination hsplit

/-- **Finitely many `σ`-classes carry a nonzero row coefficient.** -/
theorem exists_finset_rowCoeff_classes {ℓ : ℤ} (hℓ : ℓ < 0)
    (hV : MeromorphicOn (fun z => F (z + τ) - F z) Set.univ)
    (hindepR : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hVper1 : ∀ (ℓ' : ℤ), ℓ' < 0 → ∀ a : ℂ,
      laurentCoeff (fun z => F (z + τ) - F z) (a + 1) ℓ'
        = laurentCoeff (fun z => F (z + τ) - F z) a ℓ')
    (hVperσ : ∀ (ℓ' : ℤ), ℓ' < 0 → ∀ a : ℂ,
      laurentCoeff (fun z => F (z + τ) - F z) (a + σ) ℓ'
        = laurentCoeff (fun z => F (z + τ) - F z) a ℓ')
    (hfin : ∀ w : ℂ,
      {n : ℤ | laurentCoeff (fun z => F (z + τ) - F z) (w + (n : ℂ) * τ) ℓ ≠ 0}.Finite)
    (hzero : ∀ w : ℂ, ∑ᶠ n : ℤ,
      laurentCoeff (fun z => F (z + τ) - F z) (w + (n : ℂ) * τ) ℓ = 0) :
    ∃ R : Finset ℂ, ∀ w : ℂ, rowCoeff F τ ℓ w ≠ 0 →
      ∃ a b : ℤ, w - ((a : ℂ) + (b : ℂ) * σ) ∈ R := by
  classical
  set V : ℂ → ℂ := fun z => F (z + τ) - F z with hVdef
  -- the pole set of `V` is invariant under the lattice `ℤ + ℤσ`
  have hstep : ∀ (m n : ℤ) (z : ℂ), meromorphicOrderAt V z < 0 →
      meromorphicOrderAt V (z - (m • (1 : ℂ) + n • σ)) < 0 := by
    intro m n z hz
    have hlat : ∀ (ℓ' : ℤ), ℓ' < 0 →
        laurentCoeff V (z - (m • (1 : ℂ) + n • σ)) ℓ' = laurentCoeff V z ℓ' := by
      intro ℓ' hℓ'
      have h1 : laurentCoeff V ((z - (m • (1 : ℂ) + n • σ)) + ((m : ℂ) * 1)) ℓ'
          = laurentCoeff V (z - (m • (1 : ℂ) + n • σ)) ℓ' :=
        laurentCoeff_add_zsmul_of_period (hVper1 ℓ' hℓ') _ m
      have h2 : laurentCoeff V ((z - (m • (1 : ℂ) + n • σ)) + ((m : ℂ) * 1) + ((n : ℂ) * σ)) ℓ'
          = laurentCoeff V ((z - (m • (1 : ℂ) + n • σ)) + ((m : ℂ) * 1)) ℓ' :=
        laurentCoeff_add_zsmul_of_period (hVperσ ℓ' hℓ') _ n
      have hpt : (z - (m • (1 : ℂ) + n • σ)) + ((m : ℂ) * 1) + ((n : ℂ) * σ) = z := by
        simp only [zsmul_eq_mul]
        ring
      rw [hpt] at h2
      rw [← h1, ← h2]
    obtain ⟨ℓ', hℓ', hne⟩ :=
      (meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero (hV z (Set.mem_univ z))).mp hz
    refine (meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero
      (hV _ (Set.mem_univ _))).mpr ⟨ℓ', hℓ', ?_⟩
    rw [hlat ℓ' hℓ']
    exact hne
  obtain ⟨P, hP⟩ := exists_finset_pole_classes hV hindepR hstep
  -- the transverse shift indices between two classes are bounded
  have hindep' : ∀ n m j : ℤ, (n : ℂ) * σ + (m : ℂ) * τ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0 := by
    intro n m j h
    obtain ⟨h1, h2, h3⟩ := hindep m n j (by linear_combination h)
    exact ⟨h2, h1, h3⟩
  have hDfin := finite_shift_indices (τ := σ) (σ := τ) hindep' P
  obtain ⟨M, hM⟩ := hDfin.bddAbove
  set M' : ℕ := (M + 1).toNat with hM'
  refine ⟨(P ×ˢ Finset.range M').image (fun p => p.1 - (p.2 : ℂ) * τ), fun w hw => ?_⟩
  -- forward pole
  obtain ⟨k₁, hk₁⟩ := exists_ne_zero_of_rowCoeff_ne_zero hw
  -- backward pole
  have hback : rowCoeff F τ ℓ w = ∑ᶠ j : ℕ, laurentCoeff V (w + ((-((j : ℤ) + 1) : ℤ) : ℂ) * τ) ℓ :=
    rowCoeff_eq_backward_sum (hfin w) (hzero w)
  have hj₀ : ∃ j₀ : ℕ, laurentCoeff V (w + ((-((j₀ : ℤ) + 1) : ℤ) : ℂ) * τ) ℓ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    rw [hback, finsum_congr hcon, finsum_zero] at hw
    exact hw rfl
  obtain ⟨j₀, hj₀ne⟩ := hj₀
  -- reduce both poles modulo the lattice
  have hpole₁ : meromorphicOrderAt V (w + ((k₁ : ℤ) : ℂ) * τ) < 0 :=
    meromorphicOrderAt_neg_of_laurentCoeff_ne_zero (hV _ (Set.mem_univ _))
      hℓ hk₁
  have hpole₂ : meromorphicOrderAt V (w + ((-((j₀ : ℤ) + 1) : ℤ) : ℂ) * τ) < 0 :=
    meromorphicOrderAt_neg_of_laurentCoeff_ne_zero (hV _ (Set.mem_univ _))
      hℓ hj₀ne
  obtain ⟨a₁, b₁, hq₁⟩ := hP _ hpole₁
  obtain ⟨a₂, b₂, hq₂⟩ := hP _ hpole₂
  set q₁ : ℂ := w + ((k₁ : ℤ) : ℂ) * τ - (a₁ • (1 : ℂ) + b₁ • σ) with hq₁def
  set q₂ : ℂ := w + ((-((j₀ : ℤ) + 1) : ℤ) : ℂ) * τ - (a₂ • (1 : ℂ) + b₂ • σ) with hq₂def
  -- the shift index between the two classes
  have hd : ((k₁ : ℤ) + (j₀ : ℤ) + 1) ∈ {d : ℤ | ∃ q ∈ P, ∃ q' ∈ P, ∃ a b : ℤ,
      q + (d : ℂ) * τ = q' + (a : ℂ) + (b : ℂ) * σ} := by
    refine ⟨q₂, hq₂, q₁, hq₁, a₁ - a₂, b₁ - b₂, ?_⟩
    rw [hq₁def, hq₂def]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  have hbound : (k₁ : ℤ) + (j₀ : ℤ) + 1 ≤ M := hM hd
  have hk₁lt : k₁ < M' := by
    rw [hM']
    omega
  refine ⟨a₁, b₁, ?_⟩
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range]
  refine ⟨(q₁, k₁), ⟨hq₁, hk₁lt⟩, ?_⟩
  rw [hq₁def]
  simp only [zsmul_eq_mul]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
