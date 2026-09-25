import GaloisForLFunctions.RHTower.MobiusDivisorFixedCoreProfile
import GaloisForLFunctions.RHTower.MobiusDivisorLocalizedInteractions

/-!
# Sublinear cost of one moving prime after a fixed processed core

At bounded quotient depth, a fresh prime interacts with only finitely many
product-born labels. The old fixed-core fibres in those labels are uniformly
`o(sqrt M)` while the child fibres have a source amplitude ceiling. The
complete signed insertion energy is therefore `o(M)`, uniformly over primes
whose quotient depth is bounded. No growing-core uniformity is asserted.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem fibre_zero_of_overlap (M : ℕ) (P R : Finset ℕ)
    (hnot : ¬ Disjoint R P) :
    mobiusDivisorSelectionFibre M P R = 0 := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  apply sum_eq_zero
  intro d hd
  have hne : d.primeFactors \ P ≠ R := by
    intro he
    apply hnot
    rw [← he]
    exact disjoint_left.mpr (by
      intro x hx hxp
      exact (mem_sdiff.mp hx).2 hxp)
  simp [hne]

/-- Moving-prime insertion costs `o(M)` when its quotient depth is bounded,
for each fixed nonempty processed core. -/
theorem eventually_fixedCore_movingPrimeInsertion_energy_sublinear
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (hne : P.Nonempty)
    (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ p : ℕ,
      p.Prime → p < M → p ∉ P → M / p ≤ K →
      |mobiusDivisorSelectionEnergy M (insert p P) -
        mobiusDivisorSelectionEnergy M P| ≤ ε * M := by
  let C : ℝ := (3 / 5 : ℝ) * 2 ^ (P.card - 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let A : ℝ := 2 * K * C
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let δ : ℝ := ε / (A + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hcoef : A * δ < ε := by
    calc
      A * δ = (A * ε) / (A + 1) := by dsimp [δ]; ring
      _ < ε := (div_lt_iff₀ (by linarith : 0 < A + 1)).mpr (by nlinarith only [hε])
  obtain ⟨T, hT, htail⟩ :=
    exists_mobiusDivisorSelectionFibre_uniform_head_tail P hprime hne δ hδ
  filter_upwards [eventually_ge_atTop (T * (K + 1))] with M hM
  intro p hp hpM hpP hpK
  let Labels := ((mobiusDivisorSelectionPrimes M).erase p).powerset
  let S := Labels.filter (fun R => (∏ q ∈ R, q) ≤ K)
  let f : Finset ℕ → ℝ := fun R =>
    mobiusDivisorSelectionFibre M P R *
      mobiusDivisorSelectionFibre M P (insert p R)
  have hlabel (R : Finset ℕ) (hR : R ∈ Labels) : ∀ q ∈ R, q.Prime := by
    intro q hq
    exact (mem_filter.mp (mem_erase.mp (mem_powerset.mp hR hq)).2).2
  have hpR (R : Finset ℕ) (hR : R ∈ Labels) : p ∉ R := by
    intro h
    exact (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
  have hzero (R : Finset ℕ) (hR : R ∈ Labels)
      (hKR : K < ∏ q ∈ R, q) : f R = 0 := by
    have hquot : M / p < ∏ q ∈ R, q := lt_of_le_of_lt hpK hKR
    have hcut : M ≤ ∏ q ∈ insert p R, q := by
      rw [prod_insert (hpR R hR)]
      have hh := (Nat.div_lt_iff_lt_mul hp.pos).mp hquot
      simpa only [Nat.mul_comm] using hh.le
    have hz := mobiusDivisorSelectionFibre_eq_zero_of_le_product M P
      (insert p R) hcut
    simp [f, hz]
  have hsum : (∑ R ∈ Labels, f R) = ∑ R ∈ S, f R := by
    symm
    apply sum_subset (filter_subset _ _)
    intro R hR hnot
    exact hzero R hR (by simpa [S, hR] using hnot)
  have hSprime (R : Finset ℕ) (hR : R ∈ S) : ∀ q ∈ R, q.Prime :=
    hlabel R (mem_filter.mp hR).1
  have hsmall (R : Finset ℕ) (hR : R ∈ S) :
      |mobiusDivisorSelectionFibre M P R| ≤ δ * Real.sqrt M := by
    have hprod : (∏ q ∈ R, q) ≤ K := (mem_filter.mp hR).2
    by_cases hd : Disjoint R P
    · have hprod0 : 0 < ∏ q ∈ R, q :=
        prod_pos (fun q hq => (hSprime R hR q hq).pos)
      have htailR : T ≤ M / ∏ q ∈ R, q := by
        apply (Nat.le_div_iff_mul_le hprod0).mpr
        calc
          T * ∏ q ∈ R, q ≤ T * K := Nat.mul_le_mul_left T hprod
          _ ≤ T * (K + 1) := Nat.mul_le_mul_left T (Nat.le_succ K)
          _ ≤ M := hM
      exact htail M R (hSprime R hR) hd htailR
    · rw [fibre_zero_of_overlap M P R hd]
      simpa using mul_nonneg hδ.le (Real.sqrt_nonneg (M : ℝ))
  have hlarge (R : Finset ℕ) (hR : R ∈ S) :
      |mobiusDivisorSelectionFibre M P (insert p R)| ≤ C * Real.sqrt M := by
    have hRp : ∀ q ∈ insert p R, q.Prime := by
      simpa using And.intro hp (hSprime R hR)
    exact abs_mobiusDivisorSelectionFibre_le_source_amplitude M P _ hprime hRp
  have hterm (R : Finset ℕ) (hR : R ∈ S) :
      |f R| ≤ δ * C * M := by
    dsimp [f]
    rw [abs_mul]
    calc
      _ ≤ (δ * Real.sqrt M) * (C * Real.sqrt M) :=
        mul_le_mul (hsmall R hR) (hlarge R hR)
          (abs_nonneg _) (mul_nonneg hδ.le (Real.sqrt_nonneg _))
      _ = δ * C * M := by
        calc
          _ = δ * C * (Real.sqrt M * Real.sqrt M) := by ring
          _ = δ * C * M := by rw [Real.mul_self_sqrt (Nat.cast_nonneg M)]
  have hcard : S.card ≤ K := by
    simpa only [S] using mobiusDivisorProductLabel_count_le Labels K hlabel
  have hcardR : (S.card : ℝ) ≤ K := by exact_mod_cast hcard
  have hbound : |∑ R ∈ Labels, f R| ≤ (K : ℝ) * (δ * C * M) := by
    rw [hsum]
    calc
      _ ≤ ∑ R ∈ S, |f R| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _R ∈ S, δ * C * M := sum_le_sum hterm
      _ = (S.card : ℝ) * (δ * C * M) := by simp
      _ ≤ (K : ℝ) * (δ * C * M) :=
        mul_le_mul_of_nonneg_right hcardR (by positivity)
  rw [mobiusDivisorSelectionEnergy_insert_cross hp M P hpM hpP]
  have hMr : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hcoef' : 2 * (K : ℝ) * δ * C ≤ ε := by
    dsimp [A] at hcoef
    linarith
  calc
    |2 * ∑ R ∈ Labels, f R| = 2 * |∑ R ∈ Labels, f R| := by simp
    _ ≤ 2 * ((K : ℝ) * (δ * C * M)) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ ≤ ε * M := by nlinarith only [hcoef', hMr]

end RHTower
