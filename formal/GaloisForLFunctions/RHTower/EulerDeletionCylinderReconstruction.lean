import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleCylinderClosure

/-!
# Two-way finite reconstruction of Euler-deletion cylinders and ordered words

For a finite pairwise-coprime family, deletion channels indexed by subset products and pointwise
products indexed by subsets reconstruct each other by the same alternating subset coefficients.
Every strict chronological word transports letter by letter under these source identities,
including arbitrary choices of conjugated letters. All lengths and finite cutoffs are covered.

This identifies the finite source presentations; it does not assert bounded coordinate changes
uniformly over growing families or any infinite chronological completion.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace RHTower.DeletionCylinderReconstruction

theorem one_sub_prod_one_sub {ι R : Type*} [DecidableEq ι] [CommRing R]
    (B : Finset ι) (g : ι → R) :
    1 - ∏ p ∈ B, (1 - g p) =
      ∑ S ∈ B.powerset.erase ∅, (-1 : R) ^ (S.card+1) * ∏ p ∈ S, g p := by
  have hp := Finset.prod_sub (fun _ : ι => (1 : R)) g B
  simp only [Finset.prod_const_one, mul_one] at hp
  have hempty : (∅ : Finset ι) ∈ B.powerset := by simp
  rw [← Finset.sum_erase_add B.powerset
    (fun S => (-1 : R) ^ S.card * ∏ p ∈ S, g p) hempty] at hp
  simp only [Finset.card_empty, pow_zero, Finset.prod_empty, mul_one] at hp
  rw [hp]
  calc
    1 - ((∑ S ∈ B.powerset.erase ∅, (-1 : R) ^ S.card * ∏ p ∈ S, g p) + 1) =
      -(∑ S ∈ B.powerset.erase ∅, (-1 : R) ^ S.card * ∏ p ∈ S, g p) := by ring
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro S _
      rw [pow_succ]
      ring

/-- A single product-modulus coefficient reconstructs from the finite cylinder products. -/
theorem blockDeletionCoefficient_product_eq_cylinders
    (B : Finset ℕ) (hpair : (B : Set ℕ).Pairwise Nat.Coprime) (n : ℕ) :
    blockDeletionCoefficient (∏ p ∈ B, p) n =
      ∑ S ∈ B.powerset.erase ∅,
        (-1 : ℤ) ^ (S.card+1) * ∏ p ∈ S, blockDeletionCoefficient p n := by
  rw [← one_sub_prod_one_sub]
  have hdvd := finset_prod_dvd_iff_of_pairwise_coprime B hpair n
  have hp : (∏ p ∈ B, (1 - blockDeletionCoefficient p n)) =
      (∏ p ∈ B, (p : ℤ)) * (if (∏ p ∈ B, p) ∣ n then 1 else 0) := by
    simp only [blockDeletionCoefficient, sub_sub_cancel, Finset.prod_mul_distrib,
      Finset.prod_boole]
    simp only [hdvd]
  rw [hp, blockDeletionCoefficient]
  push_cast
  rfl

/-- Strictly ordered finite word, retaining its complete chronological domain. -/
def orderedWord {ι : Type*} (x : ι → ℕ → ℂ) {k : ℕ} (w : Fin k → ι) (N : ℕ) : ℂ :=
  ∑ f : Fin k → Fin N, if StrictMono f then ∏ j, x (w j) (f j) else 0

/-- A finite linear source change acts independently at every chronological word position. -/
theorem orderedWord_linear_coordinates {ι κ : Type*} [Fintype ι]
    (c : κ → ι → ℂ) (x : ι → ℕ → ℂ) {k : ℕ} (w : Fin k → κ) (N : ℕ) :
    orderedWord (fun j n => ∑ i, c j i * x i n) w N =
      ∑ a : Fin k → ι, (∏ j, c (w j) (a j)) * orderedWord x a N := by
  classical
  unfold orderedWord
  simp only [Fintype.prod_sum]
  have hf (f : Fin k → Fin N) :
      (if StrictMono f then ∑ a : Fin k → ι, ∏ j, c (w j) (a j) * x (a j) (f j) else 0) =
        ∑ a : Fin k → ι,
          (∏ j, c (w j) (a j)) * (if StrictMono f then ∏ j, x (a j) (f j) else 0) := by
    by_cases hs : StrictMono f
    · simp only [if_pos hs, Finset.prod_mul_distrib]
    · simp [hs]
  simp_rw [hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

theorem weighted_product_channel_eq_cylinders
    (B : Finset ℕ) (hpos : ∀ p ∈ B, 0 < p)
    (hpair : (B : Set ℕ).Pairwise Nat.Coprime) (s : ℂ) (n : ℕ) :
    eulerDeletionWeightedJump ((∏ p ∈ B, p)-1) s n =
      ∑ S ∈ B.powerset.erase ∅, ((-1 : ℤ) ^ (S.card+1) : ℂ) *
        eulerDeletionCylinderWeightedJump S s n := by
  rw [eulerDeletionWeightedJump_pred (Finset.prod_pos hpos),
    blockDeletionCoefficient_product_eq_cylinders B hpair]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  simp only [eulerDeletionCylinderWeightedJump]
  push_cast
  ring

abbrev CylinderIndex (F : Finset ℕ) := ↥(F.powerset.erase ∅)

def coordinate (F : Finset ℕ) (i j : CylinderIndex F) : ℂ :=
  if j.val ⊆ i.val then ((-1 : ℤ) ^ (j.val.card+1) : ℂ) else 0

def baseSource (F : Finset ℕ) (s : ℂ) (i : CylinderIndex F) (n : ℕ) : ℂ :=
  eulerDeletionWeightedJump ((∏ p ∈ i.val, p)-1) s n

def cylinderSource (F : Finset ℕ) (s : ℂ) (i : CylinderIndex F) (n : ℕ) : ℂ :=
  eulerDeletionCylinderWeightedJump i.val s n

theorem index_subset {F : Finset ℕ} (i : CylinderIndex F) : i.val ⊆ F :=
  Finset.mem_powerset.mp (Finset.mem_of_mem_erase i.property)

theorem index_nonempty {F : Finset ℕ} (i : CylinderIndex F) : i.val.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp i.property).1

theorem subset_sum {R : Type*} [AddCommMonoid R]
    (F S : Finset ℕ) (hS : S ⊆ F) (f : Finset ℕ → R) :
    (∑ T : CylinderIndex F, if T.val ⊆ S then f T.val else 0) =
      ∑ T ∈ S.powerset.erase ∅, f T := by
  calc
    _ = ∑ T ∈ F.powerset.erase ∅, if T ⊆ S then f T else 0 := Finset.sum_coe_sort _ _
    _ = _ := ?_
  rw [← Finset.sum_filter]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext T
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hne, _⟩, hTS⟩
    exact ⟨hne, hTS⟩
  · rintro ⟨hne, hTS⟩
    exact ⟨⟨hne, hTS.trans hS⟩, hTS⟩

theorem cylinderSource_eq_coordinates (F : Finset ℕ) (hpos : ∀ p ∈ F, 0 < p)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (s : ℂ) (i : CylinderIndex F) (n : ℕ) :
    cylinderSource F s i n = ∑ j : CylinderIndex F, coordinate F i j * baseSource F s j n := by
  have hi := index_subset i
  have hposi : ∀ p ∈ i.val, 0 < p := fun p hp => hpos p (hi hp)
  have hpairi : (i.val : Set ℕ).Pairwise Nat.Coprime :=
    fun _ hp _ hq hpq => hpair (hi hp) (hi hq) hpq
  rw [cylinderSource, eulerDeletionCylinderWeightedJump_eq_alternating
    i.val (index_nonempty i) hposi hpairi]
  symm
  simp only [coordinate, baseSource, ite_mul, zero_mul]
  exact subset_sum F i.val hi (fun S => ((-1 : ℤ) ^ (S.card+1) : ℂ) *
    eulerDeletionWeightedJump ((∏ p ∈ S, p)-1) s n)

theorem baseSource_eq_coordinates (F : Finset ℕ) (hpos : ∀ p ∈ F, 0 < p)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (s : ℂ) (i : CylinderIndex F) (n : ℕ) :
    baseSource F s i n = ∑ j : CylinderIndex F, coordinate F i j * cylinderSource F s j n := by
  have hi := index_subset i
  have hposi : ∀ p ∈ i.val, 0 < p := fun p hp => hpos p (hi hp)
  have hpairi : (i.val : Set ℕ).Pairwise Nat.Coprime :=
    fun _ hp _ hq hpq => hpair (hi hp) (hi hq) hpq
  rw [baseSource, weighted_product_channel_eq_cylinders i.val hposi hpairi]
  symm
  simp only [coordinate, cylinderSource, ite_mul, zero_mul]
  exact subset_sum F i.val hi (fun S => ((-1 : ℤ) ^ (S.card+1) : ℂ) *
    eulerDeletionCylinderWeightedJump S s n)

/-- Every finite cylinder word reconstructs from the original product-modulus channels. -/
theorem cylinder_orderedWord_eq_base (F : Finset ℕ) (hpos : ∀ p ∈ F, 0 < p)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (s : ℂ)
    {k : ℕ} (w : Fin k → CylinderIndex F) (N : ℕ) :
    orderedWord (cylinderSource F s) w N =
      ∑ a : Fin k → CylinderIndex F, (∏ j, coordinate F (w j) (a j)) *
        orderedWord (baseSource F s) a N := by
  have hf : cylinderSource F s =
      (fun i n => ∑ j : CylinderIndex F, coordinate F i j * baseSource F s j n) := by
    funext i n
    exact cylinderSource_eq_coordinates F hpos hpair s i n
  rw [hf]
  exact orderedWord_linear_coordinates (coordinate F) (baseSource F s) w N

/-- The original channel words reconstruct back from cylinder words at every length and cutoff. -/
theorem base_orderedWord_eq_cylinder (F : Finset ℕ) (hpos : ∀ p ∈ F, 0 < p)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (s : ℂ)
    {k : ℕ} (w : Fin k → CylinderIndex F) (N : ℕ) :
    orderedWord (baseSource F s) w N =
      ∑ a : Fin k → CylinderIndex F, (∏ j, coordinate F (w j) (a j)) *
        orderedWord (cylinderSource F s) a N := by
  have hf : baseSource F s =
      (fun i n => ∑ j : CylinderIndex F, coordinate F i j * cylinderSource F s j n) := by
    funext i n
    exact baseSource_eq_coordinates F hpos hpair s i n
  rw [hf]
  exact orderedWord_linear_coordinates (coordinate F) (cylinderSource F s) w N

def orderedStarWord {ι : Type*} (x : ι → ℕ → ℂ) {k : ℕ}
    (w : Fin k → ι) (e : Fin k → Bool) (N : ℕ) : ℂ :=
  ∑ f : Fin k → Fin N, if StrictMono f then
    ∏ j, if e j then star (x (w j) (f j)) else x (w j) (f j) else 0

theorem orderedStarWord_linear_coordinates {ι κ : Type*} [Fintype ι]
    (c : κ → ι → ℂ) (hc : ∀ j i, star (c j i) = c j i)
    (x : ι → ℕ → ℂ) {k : ℕ} (w : Fin k → κ) (e : Fin k → Bool) (N : ℕ) :
    orderedStarWord (fun j n => ∑ i, c j i * x i n) w e N =
      ∑ a : Fin k → ι, (∏ j, c (w j) (a j)) * orderedStarWord x a e N := by
  classical
  have hj (j : Fin k) (n : ℕ) :
      (if e j then star (∑ i, c (w j) i * x i n) else ∑ i, c (w j) i * x i n) =
        ∑ i, c (w j) i * (if e j then star (x i n) else x i n) := by
    cases e j <;> simp [star_sum, star_mul', hc]
  unfold orderedStarWord
  simp_rw [hj, Fintype.prod_sum]
  have hf (f : Fin k → Fin N) :
      (if StrictMono f then ∑ a : Fin k → ι,
        ∏ j, c (w j) (a j) * (if e j then star (x (a j) (f j)) else x (a j) (f j)) else 0) =
        ∑ a : Fin k → ι, (∏ j, c (w j) (a j)) *
          (if StrictMono f then
            ∏ j, if e j then star (x (a j) (f j)) else x (a j) (f j) else 0) := by
    by_cases hs : StrictMono f
    · simp only [if_pos hs, Finset.prod_mul_distrib]
    · simp [hs]
  simp_rw [hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

theorem coordinate_star (F : Finset ℕ) (i j : CylinderIndex F) :
    star (coordinate F i j) = coordinate F i j := by
  by_cases h : j.val ⊆ i.val <;> simp [coordinate, h]

/-- Reconstruction also retains every choice of conjugated letters, including Hermitian words. -/
theorem cylinder_orderedStarWord_eq_base (F : Finset ℕ) (hpos : ∀ p ∈ F, 0 < p)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (s : ℂ)
    {k : ℕ} (w : Fin k → CylinderIndex F) (e : Fin k → Bool) (N : ℕ) :
    orderedStarWord (cylinderSource F s) w e N =
      ∑ a : Fin k → CylinderIndex F, (∏ j, coordinate F (w j) (a j)) *
        orderedStarWord (baseSource F s) a e N := by
  have hf : cylinderSource F s =
      (fun i n => ∑ j : CylinderIndex F, coordinate F i j * baseSource F s j n) := by
    funext i n
    exact cylinderSource_eq_coordinates F hpos hpair s i n
  rw [hf]
  exact orderedStarWord_linear_coordinates (coordinate F) (coordinate_star F)
    (baseSource F s) w e N

/-- Reverse reconstruction for every finite word with arbitrary conjugation choices. -/
theorem base_orderedStarWord_eq_cylinder (F : Finset ℕ) (hpos : ∀ p ∈ F, 0 < p)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (s : ℂ)
    {k : ℕ} (w : Fin k → CylinderIndex F) (e : Fin k → Bool) (N : ℕ) :
    orderedStarWord (baseSource F s) w e N =
      ∑ a : Fin k → CylinderIndex F, (∏ j, coordinate F (w j) (a j)) *
        orderedStarWord (cylinderSource F s) a e N := by
  have hf : baseSource F s =
      (fun i n => ∑ j : CylinderIndex F, coordinate F i j * cylinderSource F s j n) := by
    funext i n
    exact baseSource_eq_coordinates F hpos hpair s i n
  rw [hf]
  exact orderedStarWord_linear_coordinates (coordinate F) (coordinate_star F)
    (cylinderSource F s) w e N

/-- Exact absolute coefficient mass of one subset-coordinate row. -/
theorem coordinate_norm_sum (F : Finset ℕ) (i : CylinderIndex F) :
    (∑ j : CylinderIndex F, ‖coordinate F i j‖) = (2 : ℝ) ^ i.val.card - 1 := by
  have hn (j : CylinderIndex F) :
      ‖coordinate F i j‖ = if j.val ⊆ i.val then (1 : ℝ) else 0 := by
    by_cases h : j.val ⊆ i.val <;> simp [coordinate, h, norm_pow]
  simp_rw [hn]
  rw [subset_sum F i.val (index_subset i) (fun _ => (1 : ℝ))]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem (show (∅ : Finset ℕ) ∈ i.val.powerset by simp), Finset.card_powerset]
  have hpow : 1 ≤ (2 : ℕ) ^ i.val.card := by
    have hp : 0 < (2 : ℕ) ^ i.val.card := by positivity
    omega
  rw [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

/-- Coefficient mass multiplies across all word positions, exposing the finite expansion cost. -/
theorem orderedWord_coefficient_norm_sum (F : Finset ℕ) {k : ℕ}
    (w : Fin k → CylinderIndex F) :
    (∑ a : Fin k → CylinderIndex F, ‖∏ j, coordinate F (w j) (a j)‖) =
      ∏ j, ((2 : ℝ) ^ (w j).val.card - 1) := by
  simp_rw [norm_prod]
  calc
    _ = ∏ j, ∑ a : CylinderIndex F, ‖coordinate F (w j) a‖ :=
      (Fintype.prod_sum (fun (j : Fin k) (a : CylinderIndex F) => ‖coordinate F (w j) a‖)).symm
    _ = _ := by simp_rw [coordinate_norm_sum]

/-- All channels close under the same chronological cutoff. -/
def ZeroEndpoints {ι : Type*} (x : ι → ℕ → ℂ) : Prop :=
  ∀ i, Tendsto (fun N => ∑ n ∈ Finset.range N, x i n) atTop (nhds 0)

theorem zeroEndpoints_of_coordinates {ι κ : Type*} [Fintype ι]
    (c : κ → ι → ℂ) (x : κ → ℕ → ℂ) (y : ι → ℕ → ℂ)
    (hc : ∀ i n, x i n = ∑ j, c i j * y j n) (hy : ZeroEndpoints y) :
    ZeroEndpoints x := by
  classical
  intro i
  have hp (N : ℕ) :
      (∑ n ∈ Finset.range N, x i n) = ∑ j, c i j * ∑ n ∈ Finset.range N, y j n := by
    simp_rw [hc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  have ht : Tendsto (fun N => ∑ j, c i j * ∑ n ∈ Finset.range N, y j n)
      atTop (nhds 0) := by
    have hj (j : ι) (_ : j ∈ (Finset.univ : Finset ι)) :
        Tendsto (fun N => c i j * ∑ n ∈ Finset.range N, y j n) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul (hy j)
    simpa using tendsto_finsetSum Finset.univ hj
  exact ht.congr (fun N => (hp N).symm)

/-- Simultaneous finite-cylinder closure is exactly the original product-channel closure. -/
theorem cylinder_zeroEndpoints_iff_base (F : Finset ℕ) (hpos : ∀ p ∈ F, 0 < p)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (s : ℂ) :
    ZeroEndpoints (cylinderSource F s) ↔ ZeroEndpoints (baseSource F s) := by
  constructor
  · exact zeroEndpoints_of_coordinates (coordinate F) (baseSource F s) (cylinderSource F s)
      (baseSource_eq_coordinates F hpos hpair s)
  · exact zeroEndpoints_of_coordinates (coordinate F) (cylinderSource F s) (baseSource F s)
      (cylinderSource_eq_coordinates F hpos hpair s)

end RHTower.DeletionCylinderReconstruction

