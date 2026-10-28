import GaloisForLFunctions.SignedArithmeticHodgeTheory.RamanujanFamiliesHaveAnExplicitLocalCaptureCost
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRenormalizedPrimeEnergyControlsTheDefect

/-!
# Bounded prime energy escapes fixed integer windows

Actual renormalized-prime-energy sublevels have finite Ramanujan approximation.
Local modal capture then forces their unit vectors to lose all mass in every
fixed integer window. This concerns the literal integer-coordinate norm.
-/

noncomputable section

open Filter Topology Finset
open scoped BigOperators

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open RenormalizedArithmeticPotentialTheory

/-- Mass in the first `L` integer coordinates of the actual horizon vector. -/
def primeHorizonWindowMass {N : ℕ} (L : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) : ℝ :=
  ∑ n ∈ Icc 1 L, primeHorizonExtension x n ^ 2

theorem primeHorizonWindowMass_nonneg {N : ℕ} (L : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    0 ≤ primeHorizonWindowMass L x := sum_nonneg fun _ _ => sq_nonneg _

/-- An included coordinate window cannot contain more than the total mass. -/
theorem primeHorizonWindowMass_le_norm_sq {L N : ℕ} (hLN : L ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeHorizonWindowMass L x ≤ ‖x‖ ^ 2 := by
  rw [← sum_primeHorizonExtension_sq]
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hLN)
    (fun _ _ _ => sq_nonneg _)

/-- Approximation pays local source mass through the same global error. -/
theorem primeHorizonWindowMass_le_approximation_cost {L N : ℕ} (hLN : L ≤ N)
    (x v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeHorizonWindowMass L x ≤ 2 * ‖x - v‖ ^ 2 + 2 * primeHorizonWindowMass L v := by
  have hext (n : ℕ) : primeHorizonExtension (x - v) n =
      primeHorizonExtension x n - primeHorizonExtension v n := by
    by_cases hn : n ∈ Icc 1 N
    · simp only [primeHorizonExtension, dif_pos hn, PiLp.sub_apply]
    · simp only [primeHorizonExtension, dif_neg hn, sub_self]
  calc
    _ ≤ ∑ n ∈ Icc 1 L,
        (2 * primeHorizonExtension (x - v) n ^ 2 + 2 * primeHorizonExtension v n ^ 2) := by
      apply sum_le_sum
      intro n _
      rw [hext]
      nlinarith only [sq_nonneg (primeHorizonExtension x n - 2 * primeHorizonExtension v n)]
    _ = 2 * primeHorizonWindowMass L (x - v) + 2 * primeHorizonWindowMass L v := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (primeHorizonWindowMass_le_norm_sq hLN (x - v)) zero_le_two)
      le_rfl

private def positiveConductorImage (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) : Finset ℕ+ :=
  S.attach.image (fun m => (⟨m.val, hS m.val m.property⟩ : ℕ+))

private theorem sum_positiveConductorImage {V : Type*} [AddCommMonoid V]
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (f : ℕ → V) :
    (∑ m ∈ positiveConductorImage S hS, f (m : ℕ)) = ∑ m ∈ S, f m := by
  rw [positiveConductorImage, sum_image]
  · exact sum_attach S f
  · intro x _ y _ hxy
    exact Subtype.ext (congrArg (fun m : ℕ+ => (m : ℕ)) hxy)

private theorem ramanujanFamily_apply (S : Finset ℕ+) (c : ℕ+ → ℝ) (N : ℕ)
    (n : PrimeHorizonIndex N) :
    (∑ m ∈ S, c m • ramanujanHorizonVector m N) n =
      ∑ m ∈ S, c m * ramanujanPoleProfile m n := by
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n)
    (∑ m ∈ S, c m • ramanujanHorizonVector m N) = _
  rw [map_sum]
  exact sum_congr rfl fun _ _ => rfl

private theorem ramanujanFamily_norm_sq (S : Finset ℕ+) (c : ℕ+ → ℝ) (N : ℕ) :
    ‖∑ m ∈ S, c m • ramanujanHorizonVector m N‖ ^ 2 =
      ∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ n : PrimeHorizonIndex N,
    ((∑ m ∈ S, c m • ramanujanHorizonVector m N) n) ^ 2) = _
  simp only [ramanujanFamily_apply]
  exact sum_coe_sort (Icc 1 N) (fun n => (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2)

private theorem ramanujanFamily_window_mass (S : Finset ℕ+) (c : ℕ+ → ℝ)
    {L N : ℕ} (hLN : L ≤ N) :
    primeHorizonWindowMass L (∑ m ∈ S, c m • ramanujanHorizonVector m N) =
      ∑ n ∈ Icc 1 L, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2 := by
  apply sum_congr rfl
  intro n hn
  have hnN : n ∈ Icc 1 N := Icc_subset_Icc le_rfl hLN hn
  rw [primeHorizonExtension, dif_pos hnN, ramanujanFamily_apply]

/-- Every bounded actual prime-energy sublevel loses its unit mass on each fixed
integer window, uniformly over all vectors in that sublevel. -/
theorem eventually_primeHorizonWindowMass_le_of_energy_le
    (T : ℝ) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ‖x‖ = 1 → renormalizedPrimeEnergy N x ≤ T → primeHorizonWindowMass L x ≤ ε := by
  let η : ℝ := min (ε / 4) 1
  have hη : 0 < η := lt_min (by positivity) zero_lt_one
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ ε / 4 := min_le_left _ _
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_renormalizedPrimeEnergy_le T hη
  let Spos : Finset ℕ+ := positiveConductorImage S hS
  have hlocal := eventually_ramanujanPoleProfile_family_local_mass_le Spos L
    (show (0 : ℝ) < ε / 16 by positivity)
  filter_upwards [happ, hlocal, eventually_ge_atTop L] with N haN hlN hLN x hx henergy
  obtain ⟨a, ha⟩ := haN x hx henergy
  let c : ℕ+ → ℝ := fun m => a (m : ℕ)
  let v : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    ∑ m ∈ Spos, c m • ramanujanHorizonVector m N
  have hv : v = ∑ m ∈ S, a m • ramanujanHorizonVector m N :=
    sum_positiveConductorImage S hS (fun m => a m • ramanujanHorizonVector m N)
  have herr : ‖x - v‖ ^ 2 ≤ η := by rw [hv]; exact ha
  have herr1 : ‖x - v‖ ≤ 1 := by nlinarith only [herr, hη1, norm_nonneg (x - v)]
  have hvnorm : ‖v‖ ≤ 2 := by
    calc
      ‖v‖ = ‖x - (x - v)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - v‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [hx]; linarith only [herr1]
  have hvsq : ‖v‖ ^ 2 ≤ 4 := by
    have h := mul_le_mul hvnorm hvnorm (norm_nonneg v) zero_le_two
    nlinarith only [h]
  have hvlocal : primeHorizonWindowMass L v ≤ (ε / 16) * ‖v‖ ^ 2 := by
    change primeHorizonWindowMass L (∑ m ∈ Spos, c m • ramanujanHorizonVector m N) ≤ _
    rw [ramanujanFamily_window_mass Spos c hLN]
    change _ ≤ (ε / 16) * ‖∑ m ∈ Spos, c m • ramanujanHorizonVector m N‖ ^ 2
    rw [ramanujanFamily_norm_sq]
    exact hlN c
  have hmass := primeHorizonWindowMass_le_approximation_cost hLN x v
  have hvlocal' : primeHorizonWindowMass L v ≤ ε / 4 := by
    have h := mul_le_mul_of_nonneg_left hvsq (show 0 ≤ ε / 16 by positivity)
    nlinarith only [hvlocal, h]
  nlinarith only [hmass, herr, hηε, hvlocal']

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.primeHorizonWindowMass_le_approximation_cost
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.eventually_primeHorizonWindowMass_le_of_energy_le
