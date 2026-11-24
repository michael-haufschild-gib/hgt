import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.Response

/-! # Insertion of a fixed block into a physical occupation law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- Push the law forward along the injection of occupations n ↦ an. -/
def insertedMass (a : ℕ+) (μ : ℕ+ → ℝ) : ℕ+ → ℝ :=
  Function.extend (fun n : ℕ+ => a*n) μ (fun _ => 0)

private theorem label_mul_injective (a : ℕ+) : Function.Injective (fun n : ℕ+ => a*n) :=
  fun _ _ h => mul_left_cancel h

theorem insertedMass_at (a n : ℕ+) (μ : ℕ+ → ℝ) : insertedMass a μ (a*n) = μ n :=
  (label_mul_injective a).extend_apply _ _ _

theorem insertedMass_off (a n : ℕ+) (μ : ℕ+ → ℝ) (h : n ∉ Set.range (fun k : ℕ+ => a*k)) :
    insertedMass a μ n = 0 := Function.extend_apply' _ _ _ h

theorem insertedMass_below (a n : ℕ+) (μ : ℕ+ → ℝ) (h : (n:ℕ) < (a:ℕ)) :
    insertedMass a μ n = 0 := by
  apply insertedMass_off
  rintro ⟨k,rfl⟩
  exact h.not_ge (Nat.le_mul_of_pos_right _ k.pos)

theorem insertedMass_nonneg (a : ℕ+) {μ : ℕ+ → ℝ} (hμ : ∀ n, 0 ≤ μ n) (n : ℕ+) :
    0 ≤ insertedMass a μ n := by
  by_cases h : n ∈ Set.range (fun k : ℕ+ => a*k)
  · obtain ⟨k,rfl⟩ := h
    rw [insertedMass_at]
    exact hμ k
  · exact (insertedMass_off a n μ h).ge

/-- Reindex any summand that vanishes at unoccupied labels. -/
theorem inserted_hasSum_iff {A : Type*} [AddCommMonoid A] [TopologicalSpace A]
    (a : ℕ+) (μ : ℕ+ → ℝ) (F : ℕ+ → ℝ → A) (hF : ∀ n, F n 0 = 0) (b : A) :
    HasSum (fun n => F n (insertedMass a μ n)) b ↔ HasSum (fun n => F (a*n) (μ n)) b := by
  let e := fun n : ℕ+ => a*n
  let f := fun n => F n (insertedMass a μ n)
  have hz (n : ℕ+) (hn : n ∉ Set.range e) : f n = 0 := by
    change F n (insertedMass a μ n) = 0
    rw [insertedMass_off a n μ hn,hF]
  change HasSum f b ↔ _
  rw [← (label_mul_injective a).hasSum_iff hz]
  have he (n : ℕ+) : (f ∘ e) n = F (a*n) (μ n) := by
    change F (a*n) (insertedMass a μ (a*n)) = _
    rw [insertedMass_at]
  exact (congrArg (fun g : ℕ+ → A => HasSum g b) (funext he)).to_iff

theorem insertedMass_hasSum (a : ℕ+) {μ : ℕ+ → ℝ} {m : ℝ} (hμ : HasSum μ m) :
    HasSum (insertedMass a μ) m := (inserted_hasSum_iff a μ (fun _ x => x) (fun _ => rfl) m).mpr hμ

/-- The reciprocal slot weight in the exteriority condition is its positive integer label. -/
theorem labelMean_summable_iff (μ : ℕ+ → ℝ) :
    Summable (fun n : ℕ+ => ((n:ℕ):ℝ)*μ n) ↔ Summable (fun k => μ (number k)/occupationWeight k) := by
  rw [← Equiv.pnatEquivNat.symm.summable_iff (f := fun n : ℕ+ => ((n:ℕ):ℝ)*μ n)]
  have he (k : ℕ) : ((number k).val:ℝ)*μ (number k) = μ (number k)/occupationWeight k := by
    rw [occupationWeight_eq,div_inv_eq_mul]
    change ((k+1:ℕ):ℝ)*μ (number k) = _
    push_cast
    ring
  exact (congrArg Summable (funext he)).to_iff

theorem exterior_labelMean (ρ : ExteriorLaw) : ¬ Summable (fun n : ℕ+ => ((n:ℕ):ℝ)*ρ.val n) :=
  fun h => ρ.property.2.2 ((labelMean_summable_iff ρ.val).mp h)

theorem insertedMean_iff (a : ℕ+) (μ : ℕ+ → ℝ) :
    Summable (fun n : ℕ+ => ((n:ℕ):ℝ)*insertedMass a μ n) ↔
      Summable (fun n : ℕ+ => ((n:ℕ):ℝ)*μ n) := by
  have h : Summable (fun n : ℕ+ => ((n:ℕ):ℝ)*insertedMass a μ n) ↔
      Summable (fun n : ℕ+ => (((a*n).val:ℕ):ℝ)*μ n) :=
    exists_congr (fun b => inserted_hasSum_iff a μ (fun n x => (n.val:ℝ)*x) (fun _ => mul_zero _) b)
  rw [h]
  simp only [PNat.mul_coe,Nat.cast_mul,mul_assoc]
  exact summable_mul_left_iff (by exact_mod_cast a.ne_zero : (a.val:ℝ) ≠ 0)

/-- Physical exterior preparation after insertion, including its infinite mean label. -/
def insertedExterior (a : ℕ+) (ρ : ExteriorLaw) : ExteriorLaw := by
  have hμ : HasSum ρ.val 1 := Equiv.pnatEquivNat.symm.hasSum_iff.mp ρ.property.2.1
  exact ⟨insertedMass a ρ.val,insertedMass_nonneg a ρ.property.1,
    Equiv.pnatEquivNat.symm.hasSum_iff.mpr (insertedMass_hasSum a hμ),
    fun h => exterior_labelMean ρ ((insertedMean_iff a _).mp ((labelMean_summable_iff _).mpr h))⟩

/-- A positive fraction of an exterior spectrum suffices to force an infinite mean label. -/
theorem exterior_mean_of_dominates (ρ : ExteriorLaw) {ν : ℕ+ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ n, c*ρ.val n ≤ ν n) : ¬ Summable (fun n : ℕ+ => ((n:ℕ):ℝ)*ν n) := by
  intro hs
  apply exterior_labelMean ρ
  apply (summable_mul_left_iff hc.ne').mp
  apply hs.of_nonneg_of_le (fun n => mul_nonneg hc.le (mul_nonneg (Nat.cast_nonneg _) (ρ.property.1 n)))
  intro n
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (h n) (Nat.cast_nonneg _)

#print axioms insertedMass_at
#print axioms insertedMass_off
#print axioms insertedMass_below
#print axioms insertedMass_nonneg
#print axioms inserted_hasSum_iff
#print axioms insertedMass_hasSum
#print axioms labelMean_summable_iff
#print axioms exterior_labelMean
#print axioms insertedMean_iff
#print axioms exterior_mean_of_dominates

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
