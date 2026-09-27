import GaloisForLFunctions.RHTower.LogarithmicMobiusReconstruction
import GaloisForLFunctions.RHTower.EulerDeletionCoprimeKernelDiagonalization

/-!
# Coprime energy of finite logarithmic histories

The existing finite coprime-kernel diagonalization is transported to
logarithmic delay profiles. Möbius inversion of the squared dilation sum
keeps exactly the coprime pairs. Their only nonzero diagonal is the
original endpoint; every other surviving term is retained as a cross term.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def logarithmicCoprimeEnergy (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊Real.exp T⌋₊) ×ˢ (Finset.Icc 1 ⌊Real.exp T⌋₊),
    (if p.1.Coprime p.2 then (1 : ℝ) else 0) *
      (f (T - Real.log p.1) * f (T - Real.log p.2))

def logarithmicCoprimeCross (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∑ p ∈ ((Finset.Icc 1 ⌊Real.exp T⌋₊) ×ˢ (Finset.Icc 1 ⌊Real.exp T⌋₊)).filter
      (fun p => p.1 ≠ p.2),
    (if p.1.Coprime p.2 then (1 : ℝ) else 0) *
      (f (T - Real.log p.1) * f (T - Real.log p.2))

/-- A filtered sum over multiples is one exact logarithmic dilation. -/
theorem logarithmicDilationSum_eq_filteredMultiples (f : ℝ → ℝ) (T : ℝ)
    {n : ℕ} (hn : 0 < n) :
    (∑ m ∈ (Finset.Icc 1 ⌊Real.exp T⌋₊).filter (fun m => n ∣ m),
      f (T - Real.log m)) = logarithmicDilationSum f (T - Real.log n) := by
  rw [sum_Icc_filter_dvd_reindex n _ hn]
  unfold logarithmicDilationSum logarithmicWeightedDilation
  rw [Real.exp_sub, Real.exp_log (by exact_mod_cast hn), Nat.floor_div_natCast]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  rw [one_mul, Nat.cast_mul, Real.log_mul (by exact_mod_cast hn.ne')
    (by exact_mod_cast hmpos.ne'), sub_sub]

private theorem interval_divisor_union (N : ℕ) :
    (Finset.Icc 1 N).biUnion Nat.divisors = Finset.Icc 1 N := by
  ext d
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨m, hm, hdm, _⟩
    exact ⟨Nat.pos_of_dvd_of_pos hdm hm.1, (Nat.le_of_dvd hm.1 hdm).trans hm.2⟩
  · intro hd
    exact ⟨d, hd, dvd_rfl, Nat.ne_of_gt hd.1⟩

/-- Exact arithmetic cancellation of all pairs with a nontrivial common
divisor. This is a signed identity, not a positivity assertion. -/
theorem logarithmicCoprimeEnergy_eq_mobius_square_dilation (f : ℝ → ℝ) (T : ℝ) :
    logarithmicCoprimeEnergy f T =
      logarithmicMobiusInverse (fun t => logarithmicDilationSum f t ^ 2) T := by
  let S := Finset.Icc 1 ⌊Real.exp T⌋₊
  let a : ℕ → ℝ := fun n => (n : ℝ) * f (T - Real.log n)
  have ha (n : ℕ) (hn : n ∈ S) : a n / (n : ℝ) = f (T - Real.log n) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
    dsimp only [a]
    field_simp
  have h := Sieve.sum_coprime_diagonal S (fun n hn => (Finset.mem_Icc.mp hn).1) a
  have hl : logarithmicCoprimeEnergy f T =
      ∑ p ∈ S ×ˢ S, (if p.1.Coprime p.2 then (1 : ℝ) else 0) *
        ((a p.1 / (p.1 : ℝ)) * (a p.2 / (p.2 : ℝ))) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [ha p.1 (Finset.mem_product.mp hp).1, ha p.2 (Finset.mem_product.mp hp).2]
  rw [hl, h, show S.biUnion Nat.divisors = S from interval_divisor_union _]
  unfold logarithmicMobiusInverse logarithmicWeightedDilation
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hfilter : (∑ m ∈ S.filter (fun m => n ∣ m), a m / (m : ℝ)) =
      ∑ m ∈ S.filter (fun m => n ∣ m), f (T - Real.log m) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact ha m (Finset.mem_filter.mp hm).1
  rw [hfilter, logarithmicDilationSum_eq_filteredMultiples f T hnpos]

/-- Only the endpoint survives on the coprime diagonal. -/
theorem logarithmicCoprimeEnergy_eq_endpoint_add_cross (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    logarithmicCoprimeEnergy f T = f T ^ 2 + logarithmicCoprimeCross f T := by
  let S := (Finset.Icc 1 ⌊Real.exp T⌋₊) ×ˢ (Finset.Icc 1 ⌊Real.exp T⌋₊)
  let w : ℕ × ℕ → ℝ := fun p => (if p.1.Coprime p.2 then (1 : ℝ) else 0) *
    (f (T - Real.log p.1) * f (T - Real.log p.2))
  have hN : 1 ≤ ⌊Real.exp T⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  have hmem : (1, 1) ∈ S := Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨le_rfl, hN⟩, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩
  have hd : (∑ p ∈ S, if p.1 = p.2 then w p else 0) = f T ^ 2 := by
    rw [Finset.sum_eq_single (1, 1)]
    · simp [w, sq]
    · rintro ⟨a, b⟩ _ hne
      by_cases hab : a = b
      · subst b
        have ha : a ≠ 1 := by intro ha; apply hne; simp [ha]
        simp [w, Nat.coprime_self, ha]
      · simp [hab]
    · exact fun h => (h hmem).elim
  have hs : (∑ p ∈ S, w p) =
      (∑ p ∈ S, if p.1 = p.2 then w p else 0) +
        ∑ p ∈ S.filter (fun p => p.1 ≠ p.2), w p := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.1 = p.2 <;> simp [hp]
  exact hs.trans (congrArg (fun x => x + logarithmicCoprimeCross f T) hd)

/-- The complete coprime energy of a reconstructed profile is the signed
Möbius transform of the squared source, at every real terminal time. -/
theorem logarithmicCoprimeEnergy_mobiusInverse (f : ℝ → ℝ) (T : ℝ) :
    logarithmicCoprimeEnergy (logarithmicMobiusInverse f) T =
      logarithmicMobiusInverse (fun t => f t ^ 2) T := by
  rw [logarithmicCoprimeEnergy_eq_mobius_square_dilation]
  unfold logarithmicMobiusInverse logarithmicWeightedDilation
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hnT : (n : ℝ) ≤ Real.exp T :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2
  have ht : 0 ≤ T - Real.log n := sub_nonneg.mpr ((Real.log_le_iff_le_exp hnpos).mpr hnT)
  change _ * logarithmicDilationSum (logarithmicMobiusInverse f) (T - Real.log n) ^ 2 = _
  rw [logarithmicDilationSum_mobiusInverse f ht]

end RHTower
