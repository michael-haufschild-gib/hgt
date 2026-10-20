import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiAllBoundaryTraceDirichletRayBound

/-!
# Conditioning of the all-boundary Fermi trace: the upper bound

Both physical energies split over dyadic rays `2^k b`, `b` odd: the sieve energy into the ray
sieve energies, and the all-boundary energy into the ray all-boundary energies, the twice-odd
cells supplying the bottom jump of every ray. The Dirichlet ray inequality then holds for the
whole trace with the same constant:

`P ≤ (1/λ + 1)/ρ_m · Q_all`, `λ = 2 - 2 cos(π/(log₂ N + m + 6))`, `ρ_m = 2^(m+1)/(2^(m+1)+1)`.

Since `1/λ ~ (log₂ N)²/π²`, the all-boundary inverse constant is at most
`(1 + o(1)) (log₂ N)²/(π² ρ_m)` for every fixed `m`, against the sharp `(4/π²)(log₂ N)²` of the
selected trace.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Exchange of two summation orders of a jointly summable double series. -/
private theorem tsum_swap_and_summable (F : ℕ → ℕ → ℝ)
    (h : Summable (fun p : ℕ × ℕ => F p.1 p.2)) :
    (∑' k, ∑' j, F k j) = (∑' j, ∑' k, F k j) ∧ Summable (fun j => ∑' k, F k j) := by
  have hswap : Summable (fun q : ℕ × ℕ => F q.2 q.1) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.mpr h
  have hk : ∀ k, Summable (F k) := fun k => h.prod_factor k
  have hj : ∀ j, Summable (fun k => F k j) := fun j => hswap.prod_factor j
  exact ⟨(Summable.tsum_comm' (f := F) h hk hj).symm, hswap.prod⟩

private theorem odd_ray_summable (N : ℕ) (c : ℕ → ℝ) :
    Summable (fun m : ℕ => sieveSeq N c (2 * m + 1) ^ 2 / (pronicSeq (2 * m + 1) : ℝ)) := by
  let A := ∑ d ∈ Icc 1 N, |c d|
  have hb (n : ℕ) : |sieveSeq N c n ^ 2| ≤ A ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_sieveSeq_le_sum_abs N c n) 2
  have hs := summable_div_pronicSeq_of_bounded hb
  exact hs.comp_injective (i := fun m : ℕ => 2 * m + 1)
    (by intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)

private theorem twiceOdd_summable (N : ℕ) (c : ℕ → ℝ) :
    Summable (fun m : ℕ => fermiBoundaryJump N c (4 * m + 2) ^ 2 /
      (pronicSeq (4 * m + 2) : ℝ)) := by
  let A := ∑ d ∈ Icc 1 N, |c d|
  have hb (n : ℕ) : |(2 * sieveSeq N c (n / 2) - sieveSeq N c n) ^ 2| ≤ (3 * A) ^ 2 := by
    have h1 := abs_le.mp (abs_sieveSeq_le_sum_abs N c (n / 2))
    have h2 := abs_le.mp (abs_sieveSeq_le_sum_abs N c n)
    have h : |2 * sieveSeq N c (n / 2) - sieveSeq N c n| ≤ 3 * A :=
      abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hs := (summable_div_pronicSeq_of_bounded hb).comp_injective
    (i := fun m : ℕ => 4 * m + 2) (by intro a b h; change 4 * a + 2 = 4 * b + 2 at h; omega)
  refine hs.congr fun m => ?_
  change (2 * sieveSeq N c ((4 * m + 2) / 2) - sieveSeq N c (4 * m + 2)) ^ 2 /
    (pronicSeq (4 * m + 2) : ℝ) = _
  rw [show 4 * m + 2 = 2 * (2 * m) + 2 by ring, fermiBoundaryJump_even,
    show (2 * (2 * m) + 2) / 2 = 2 * m + 1 by omega]

/-- The twice-odd cells read the bottom jump of every dyadic ray. -/
theorem fermiTwiceOddPronicEnergy_rays (N : ℕ) (c : ℕ → ℝ) :
    fermiTwiceOddPronicEnergy N c =
      ∑' j : ℕ, fermiNormalizedDyadicJump N c (2 * j + 1) 0 ^ 2 *
        fermiDyadicPronicWeight 1 (2 * j + 1) := by
  unfold fermiTwiceOddPronicEnergy
  apply tsum_congr
  intro j
  unfold fermiNormalizedDyadicJump fermiDyadicPronicWeight
  rw [show (2 : ℕ) ^ (0 + 1) * (2 * j + 1) = 4 * j + 2 by ring]
  ring

/-- The sieve energy is the sum of the ray sieve energies over odd bases. -/
theorem sieveTotalPronicEnergy_eq_sum_rays (N : ℕ) (c : ℕ → ℝ) :
    sieveTotalPronicEnergy N c = ∑' j : ℕ, fermiRaySieveEnergy N c (2 * j + 1) ∧
      Summable (fun j : ℕ => fermiRaySieveEnergy N c (2 * j + 1)) := by
  set F : ℕ → ℕ → ℝ := fun k j => fermiNormalizedDyadicSieve N c (2 * j + 1) (k + 1) ^ 2 *
    fermiDyadicPronicWeight (k + 1) (2 * j + 1)
  obtain ⟨hswap, hsum⟩ := tsum_swap_and_summable F (sieve_fermi_dyadic_pronic_summable N c).1
  have hodd := odd_ray_summable N c
  have hray (j : ℕ) : fermiRaySieveEnergy N c (2 * j + 1) =
      sieveSeq N c (2 * j + 1) ^ 2 / (pronicSeq (2 * j + 1) : ℝ) + ∑' k, F k j := by
    unfold fermiRaySieveEnergy
    rw [((fermiRay_weighted_summable N c (by omega : 0 < 2 * j + 1)).1).tsum_eq_zero_add]
    congr 1
    unfold fermiNormalizedDyadicSieve fermiDyadicPronicWeight
    simp [div_eq_mul_inv]
  have hfun : (fun j : ℕ => fermiRaySieveEnergy N c (2 * j + 1)) =
      fun j => sieveSeq N c (2 * j + 1) ^ 2 / (pronicSeq (2 * j + 1) : ℝ) + ∑' k, F k j :=
    funext hray
  refine ⟨?_, by rw [hfun]; exact hodd.add hsum⟩
  rw [sieveTotalPronicEnergy_dyadic_rays, hfun, hodd.tsum_add hsum]
  congr 1

/-- The all-boundary energy is the sum of the ray all-boundary energies over odd bases. -/
theorem fermiAllBoundaryPronicEnergy_eq_sum_rays (N : ℕ) (c : ℕ → ℝ) :
    fermiAllBoundaryPronicEnergy N c = ∑' j : ℕ, fermiRayAllBoundaryEnergy N c (2 * j + 1) ∧
      Summable (fun j : ℕ => fermiRayAllBoundaryEnergy N c (2 * j + 1)) := by
  set F : ℕ → ℕ → ℝ := fun k j => fermiNormalizedDyadicJump N c (2 * j + 1) (k + 1) ^ 2 *
    fermiDyadicPronicWeight (k + 2) (2 * j + 1)
  obtain ⟨hswap, hsum⟩ := tsum_swap_and_summable F (sieve_fermi_dyadic_pronic_summable N c).2
  have hodd := odd_ray_summable N c
  have htw : Summable (fun j : ℕ => fermiNormalizedDyadicJump N c (2 * j + 1) 0 ^ 2 *
      fermiDyadicPronicWeight 1 (2 * j + 1)) := by
    refine (twiceOdd_summable N c).congr fun j => ?_
    unfold fermiNormalizedDyadicJump fermiDyadicPronicWeight
    rw [show (2 : ℕ) ^ (0 + 1) * (2 * j + 1) = 4 * j + 2 by ring]
    ring
  have hray (j : ℕ) : fermiRayAllBoundaryEnergy N c (2 * j + 1) =
      sieveSeq N c (2 * j + 1) ^ 2 / (pronicSeq (2 * j + 1) : ℝ) +
        (fermiNormalizedDyadicJump N c (2 * j + 1) 0 ^ 2 *
          fermiDyadicPronicWeight 1 (2 * j + 1) + ∑' k, F k j) := by
    unfold fermiRayAllBoundaryEnergy
    rw [((fermiRay_weighted_summable N c (by omega : 0 < 2 * j + 1)).2).tsum_eq_zero_add]
    congr 1
    unfold fermiNormalizedDyadicSieve fermiDyadicPronicWeight
    simp [div_eq_mul_inv]
  have hfun : (fun j : ℕ => fermiRayAllBoundaryEnergy N c (2 * j + 1)) =
      fun j => sieveSeq N c (2 * j + 1) ^ 2 / (pronicSeq (2 * j + 1) : ℝ) +
        (fermiNormalizedDyadicJump N c (2 * j + 1) 0 ^ 2 *
          fermiDyadicPronicWeight 1 (2 * j + 1) + ∑' k, F k j) :=
    funext hray
  refine ⟨?_, by rw [hfun]; exact hodd.add (htw.add hsum)⟩
  unfold fermiAllBoundaryPronicEnergy
  rw [fermiSelectedTotalPronicEnergy_dyadic_rays, fermiTwiceOddPronicEnergy_rays, hfun,
    hodd.tsum_add (htw.add hsum), htw.tsum_add hsum]
  rw [hswap]
  ring

/-- The constant of the Dirichlet ray inequality at horizon `N` and cutoff `m`. -/
def fermiAllBoundaryRayConstant (N m : ℕ) : ℝ :=
  (1 / (2 - 2 * Real.cos (Real.pi / (((Nat.log 2 N + 1 + m + 4 : ℕ) : ℝ) + 1))) + 1) /
    fermiRayWeightFloor m

/-- **All-boundary observability bound.** For every coefficient vector and cutoff
`m ≤ log₂ N + 1`, the physical sieve energy is at most the ray constant times the physical
all-boundary trace energy. -/
theorem sieveTotalPronicEnergy_le_allBoundary (N : ℕ) (c : ℕ → ℝ) (m : ℕ)
    (hm : m ≤ Nat.log 2 N + 1) :
    sieveTotalPronicEnergy N c ≤ fermiAllBoundaryRayConstant N m *
      fermiAllBoundaryPronicEnergy N c := by
  obtain ⟨hP, hPs⟩ := sieveTotalPronicEnergy_eq_sum_rays N c
  obtain ⟨hQ, hQs⟩ := fermiAllBoundaryPronicEnergy_eq_sum_rays N c
  rw [hP, hQ, ← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun j => fermiRaySieveEnergy_le_allBoundary N c (by omega : 0 < 2 * j + 1) m hm) hPs
    (hQs.mul_left _)

/-! ### The all-boundary inverse constants -/

/-- Physical sieve/all-boundary ratios over coefficient vectors in `D` with positive trace. -/
def fermiAllBoundaryRatios (N : ℕ) (D : Set (ℕ → ℝ)) : Set ℝ :=
  {t | ∃ c ∈ D, 0 < fermiAllBoundaryPronicEnergy N c ∧
    t = sieveTotalPronicEnergy N c / fermiAllBoundaryPronicEnergy N c}

/-- Optimal physical inverse constant of the all-boundary trace. -/
def fermiAllBoundaryInverseConstant (N : ℕ) : ℝ := sSup (fermiAllBoundaryRatios N Set.univ)

/-- The same constant over pointwise nonnegative coefficients. -/
def fermiNonnegativeAllBoundaryInverseConstant (N : ℕ) : ℝ :=
  sSup (fermiAllBoundaryRatios N {c | ∀ d, 0 ≤ c d})

theorem fermiAllBoundaryRayConstant_nonneg (N m : ℕ) : 0 ≤ fermiAllBoundaryRayConstant N m := by
  unfold fermiAllBoundaryRayConstant
  have hρ := fermiRayWeightFloor_pos m
  have hc := Real.cos_le_one (Real.pi / (((Nat.log 2 N + 1 + m + 4 : ℕ) : ℝ) + 1))
  have : 0 ≤ 1 / (2 - 2 * Real.cos (Real.pi / (((Nat.log 2 N + 1 + m + 4 : ℕ) : ℝ) + 1))) :=
    div_nonneg zero_le_one (by linarith)
  positivity

theorem fermiAllBoundaryRatio_le (N : ℕ) (D : Set (ℕ → ℝ)) (m : ℕ)
    (hm : m ≤ Nat.log 2 N + 1) {t : ℝ} (ht : t ∈ fermiAllBoundaryRatios N D) :
    t ≤ fermiAllBoundaryRayConstant N m := by
  obtain ⟨c, -, hQ, rfl⟩ := ht
  rw [div_le_iff₀ hQ]
  exact sieveTotalPronicEnergy_le_allBoundary N c m hm

theorem fermiAllBoundaryRatios_bddAbove (N : ℕ) (D : Set (ℕ → ℝ)) :
    BddAbove (fermiAllBoundaryRatios N D) :=
  ⟨fermiAllBoundaryRayConstant N 0, fun _ ht =>
    fermiAllBoundaryRatio_le N D 0 (Nat.zero_le _) ht⟩

/-- Both all-boundary inverse constants are at most the ray constant for every admissible
cutoff. -/
theorem fermiAllBoundaryInverseConstant_le (N m : ℕ) (hm : m ≤ Nat.log 2 N + 1) :
    fermiAllBoundaryInverseConstant N ≤ fermiAllBoundaryRayConstant N m ∧
      fermiNonnegativeAllBoundaryInverseConstant N ≤ fermiAllBoundaryRayConstant N m :=
  ⟨Real.sSup_le (fun _ ht => fermiAllBoundaryRatio_le N _ m hm ht)
      (fermiAllBoundaryRayConstant_nonneg N m),
    Real.sSup_le (fun _ ht => fermiAllBoundaryRatio_le N _ m hm ht)
      (fermiAllBoundaryRayConstant_nonneg N m)⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
