import GaloisForLFunctions.RHTower.Sieve.PrimeCubeSupport

/-!
# Adapted moments of prime-supported Dirichlet polynomials

The sixth-moment level-set bound generalizes to every even moment.  The `ℓ`-th power of a
Dirichlet polynomial is again a Dirichlet polynomial, indexed by `ℓ`-tuples through the product
of their entries; for prime-supported coefficients a tuple of primes with a fixed product has
every coordinate among the at most `ℓ` prime factors of that product, so the contributing fibre
has at most `ℓ^ℓ` points and the power's `ℓ²` coefficient mass is at most `ℓ^ℓ·(∑‖b_p‖²)^ℓ`.

The resulting level-set bound

    V^{2ℓ}·|{t ∈ [-T,T] : |F(t)| ≥ V}| ≤ 2(T + 4N^ℓ(1+log N^ℓ))·ℓ^ℓ·(∑_p ‖b_p‖²)^ℓ

with `ℓ` chosen so that `N^ℓ` matches `T` is the adapted-moment count for well-spaced large
values of short prime polynomials.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The index of an `ℓ`-tuple: the product of its shifted entries, shifted down by one. -/
def powIdx {N ℓ : ℕ} (p : Fin ℓ → Fin N) : Fin (N ^ ℓ) :=
  ⟨(∏ i : Fin ℓ, ((p i : ℕ) + 1)) - 1, by
    have hle : (∏ i : Fin ℓ, ((p i : ℕ) + 1)) ≤ ∏ _i : Fin ℓ, N := by
      refine Finset.prod_le_prod' fun i _ => ?_
      exact (p i).isLt
    have hprodN : (∏ _i : Fin ℓ, N) = N ^ ℓ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hpos : 0 < ∏ i : Fin ℓ, ((p i : ℕ) + 1) :=
      Finset.prod_pos fun i _ => Nat.succ_pos _
    omega⟩

/-- The defining property of `powIdx`: it names the product. -/
theorem powIdx_val_add_one {N ℓ : ℕ} (p : Fin ℓ → Fin N) :
    ((powIdx p : ℕ) + 1) = ∏ i : Fin ℓ, ((p i : ℕ) + 1) := by
  have hpos : 0 < ∏ i : Fin ℓ, ((p i : ℕ) + 1) :=
    Finset.prod_pos fun i _ => Nat.succ_pos _
  simp only [powIdx]
  omega

/-- The `ℓ`-fold Dirichlet convolution of a coefficient vector. -/
noncomputable def convPow (N ℓ : ℕ) (a : Fin N → ℂ) : Fin (N ^ ℓ) → ℂ := fun j =>
  ∑ p ∈ (Finset.univ : Finset (Fin ℓ → Fin N)).filter (fun p => powIdx p = j),
    ∏ i : Fin ℓ, a (p i)

/-- The phase of a tuple is the phase of its product. -/
private theorem exp_phase_powIdx {N ℓ : ℕ} (t : ℝ) (p : Fin ℓ → Fin N) :
    (∏ i : Fin ℓ, Complex.exp (((t * Real.log ((p i : ℕ) + 1) : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((t * Real.log ((powIdx p : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_sum]
  congr 1
  have hcast : ((powIdx p : ℕ) : ℝ) + 1 = ∏ i : Fin ℓ, (((p i : ℕ) : ℝ) + 1) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (powIdx_val_add_one p)
  have hlog : Real.log (((powIdx p : ℕ) : ℝ) + 1)
      = ∑ i : Fin ℓ, Real.log (((p i : ℕ) : ℝ) + 1) := by
    rw [hcast]
    exact Real.log_prod fun i _ => by positivity
  rw [hlog]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

/-- **The `ℓ`-th power of a Dirichlet polynomial is a Dirichlet polynomial.** -/
theorem dirPoly_convPow (N ℓ : ℕ) (a : Fin N → ℂ) (t : ℝ) :
    dirPoly (N ^ ℓ) (convPow N ℓ a) t = (dirPoly N a t) ^ ℓ := by
  classical
  set E : Fin N → ℂ := fun n =>
    Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) with hE
  have hpow : (dirPoly N a t) ^ ℓ
      = ∑ p : Fin ℓ → Fin N, (∏ i : Fin ℓ, a (p i)) * (∏ i : Fin ℓ, E (p i)) := by
    have hpoly : dirPoly N a t = ∑ n : Fin N, a n * E n := rfl
    have hconst : (dirPoly N a t) ^ ℓ = ∏ _i : Fin ℓ, dirPoly N a t := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hconst, hpoly]
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_mul_distrib]
  have hphase : ∀ p : Fin ℓ → Fin N,
      (∏ i : Fin ℓ, a (p i)) * (∏ i : Fin ℓ, E (p i))
        = (∏ i : Fin ℓ, a (p i))
            * Complex.exp (((t * Real.log ((powIdx p : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
    intro p
    rw [hE]
    rw [exp_phase_powIdx t p]
  rw [hpow]
  simp only [hphase]
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin ℓ → Fin N)))
    (t := (Finset.univ : Finset (Fin (N ^ ℓ)))) (g := fun p => powIdx p)
    (f := fun p : Fin ℓ → Fin N => (∏ i : Fin ℓ, a (p i))
      * Complex.exp (((t * Real.log ((powIdx p : ℕ) + 1) : ℝ) : ℂ) * Complex.I))
    (fun p _ => Finset.mem_univ _)
  rw [← hfib]
  have hpoly : dirPoly (N ^ ℓ) (convPow N ℓ a) t
      = ∑ j : Fin (N ^ ℓ), convPow N ℓ a j
          * Complex.exp (((t * Real.log ((j : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := rfl
  rw [hpoly]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [convPow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [hp.2]

/-- The support-filtered fibre of the power index. -/
noncomputable def powFibreOn (N ℓ : ℕ) (S : Finset (Fin N)) (j : Fin (N ^ ℓ)) :
    Finset (Fin ℓ → Fin N) :=
  ((Finset.univ : Finset (Fin ℓ → Fin N)).filter (fun p => powIdx p = j)).filter
    (fun p => ∀ i : Fin ℓ, p i ∈ S)

/-- **The `ℓ²` mass of the `ℓ`-fold convolution, through a support.** -/
theorem sum_normSq_convPow_le_of_support (N ℓ : ℕ) (a : Fin N → ℂ) (S : Finset (Fin N))
    (hsupp : ∀ n : Fin N, a n ≠ 0 → n ∈ S) {D : ℝ}
    (hD : ∀ j : Fin (N ^ ℓ), ((powFibreOn N ℓ S j).card : ℝ) ≤ D) (hD0 : 0 ≤ D) :
    ∑ j : Fin (N ^ ℓ), ‖convPow N ℓ a j‖ ^ 2
      ≤ D * (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ := by
  classical
  set g : (Fin ℓ → Fin N) → ℝ := fun p => ‖∏ i : Fin ℓ, a (p i)‖ with hg
  have hconv : ∀ j : Fin (N ^ ℓ),
      convPow N ℓ a j = ∑ p ∈ powFibreOn N ℓ S j, ∏ i : Fin ℓ, a (p i) := by
    intro j
    rw [convPow, powFibreOn]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro p _ hne i
    exact hsupp _ ((Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i))
  have hfibre : ∀ j : Fin (N ^ ℓ),
      ‖convPow N ℓ a j‖ ^ 2 ≤ D * ∑ p ∈ powFibreOn N ℓ S j, g p ^ 2 := by
    intro j
    have hnorm : ‖convPow N ℓ a j‖ ≤ ∑ p ∈ powFibreOn N ℓ S j, g p := by
      rw [hconv j]
      exact norm_sum_le _ _
    have hsq : ‖convPow N ℓ a j‖ ^ 2 ≤ (∑ p ∈ powFibreOn N ℓ S j, g p) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hcs : (∑ p ∈ powFibreOn N ℓ S j, g p) ^ 2
        ≤ ((powFibreOn N ℓ S j).card : ℝ) * ∑ p ∈ powFibreOn N ℓ S j, g p ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hsum0 : (0 : ℝ) ≤ ∑ p ∈ powFibreOn N ℓ S j, g p ^ 2 :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    have hmul : ((powFibreOn N ℓ S j).card : ℝ) * ∑ p ∈ powFibreOn N ℓ S j, g p ^ 2
        ≤ D * ∑ p ∈ powFibreOn N ℓ S j, g p ^ 2 :=
      mul_le_mul_of_nonneg_right (hD j) hsum0
    linarith
  have hsum : ∑ j : Fin (N ^ ℓ), ‖convPow N ℓ a j‖ ^ 2
      ≤ ∑ j : Fin (N ^ ℓ), D * ∑ p ∈ powFibreOn N ℓ S j, g p ^ 2 :=
    Finset.sum_le_sum fun j _ => hfibre j
  set sSet : Finset (Fin ℓ → Fin N) :=
    (Finset.univ : Finset (Fin ℓ → Fin N)).filter (fun p => ∀ i : Fin ℓ, p i ∈ S)
    with hsSet
  have hfibreOn : ∀ j : Fin (N ^ ℓ),
      powFibreOn N ℓ S j = sSet.filter (fun p => powIdx p = j) := by
    intro j
    rw [powFibreOn, hsSet]
    exact Finset.filter_comm _ _ _
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := sSet) (t := (Finset.univ : Finset (Fin (N ^ ℓ)))) (g := fun p => powIdx p)
    (f := fun p : Fin ℓ → Fin N => g p ^ 2)
    (fun p _ => Finset.mem_univ _)
  have hcollect : ∑ j : Fin (N ^ ℓ), D * ∑ p ∈ powFibreOn N ℓ S j, g p ^ 2
      = D * ∑ p ∈ sSet, g p ^ 2 := by
    simp only [hfibreOn]
    rw [← Finset.mul_sum, hfib]
  have hmono : ∑ p ∈ sSet, g p ^ 2 ≤ ∑ p : Fin ℓ → Fin N, g p ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => sq_nonneg _)
  have hprod : ∑ p : Fin ℓ → Fin N, g p ^ 2
      = (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ := by
    have hpt : ∀ p : Fin ℓ → Fin N, g p ^ 2 = ∏ i : Fin ℓ, ‖a (p i)‖ ^ 2 := by
      intro p
      simp only [hg]
      rw [norm_prod, ← Finset.prod_pow]
    simp only [hpt]
    have hconst : (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ
        = ∏ _i : Fin ℓ, ∑ n : Fin N, ‖a n‖ ^ 2 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hconst, Finset.prod_univ_sum, Fintype.piFinset_univ]
  calc ∑ j : Fin (N ^ ℓ), ‖convPow N ℓ a j‖ ^ 2
      ≤ ∑ j : Fin (N ^ ℓ), D * ∑ p ∈ powFibreOn N ℓ S j, g p ^ 2 := hsum
    _ = D * ∑ p ∈ sSet, g p ^ 2 := hcollect
    _ ≤ D * ∑ p : Fin ℓ → Fin N, g p ^ 2 :=
        mul_le_mul_of_nonneg_left hmono hD0
    _ = D * (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ := by rw [hprod]

/-- **A prime-supported power fibre has at most `ℓ^ℓ` points.**  Every coordinate of a fibre
tuple lies among the at most `ℓ` prime factors of the anchored product. -/
private theorem powFibreOn_primeSupport_card_le (N ℓ : ℕ) (j : Fin (N ^ ℓ)) :
    ((powFibreOn N ℓ (primeSupport N) j).card : ℝ) ≤ (ℓ : ℝ) ^ ℓ := by
  classical
  have hprodEq : ∀ p ∈ powFibreOn N ℓ (primeSupport N) j,
      (∏ i : Fin ℓ, ((p i : ℕ) + 1)) = (j : ℕ) + 1 := by
    intro p hp
    rw [powFibreOn, Finset.mem_filter] at hp
    have hmem := hp.1
    rw [Finset.mem_filter] at hmem
    rw [← powIdx_val_add_one p, hmem.2]
  have hprime : ∀ p ∈ powFibreOn N ℓ (primeSupport N) j,
      ∀ i : Fin ℓ, Nat.Prime ((p i : ℕ) + 1) := by
    intro p hp i
    rw [powFibreOn, Finset.mem_filter] at hp
    have h := hp.2 i
    rw [primeSupport, Finset.mem_filter] at h
    exact h.2
  have hnat : (powFibreOn N ℓ (primeSupport N) j).card ≤ ℓ ^ ℓ := by
    rcases Finset.eq_empty_or_nonempty (powFibreOn N ℓ (primeSupport N) j) with he | hne
    · rw [he, Finset.card_empty]
      exact Nat.zero_le _
    · obtain ⟨q₀, hq₀⟩ := hne
      set T : Finset (Fin N) := Finset.image q₀ Finset.univ with hT
      have hTcard : T.card ≤ ℓ := by
        refine le_trans (Finset.card_image_le) ?_
        rw [Finset.card_univ, Fintype.card_fin]
      have hmaps : ∀ p ∈ powFibreOn N ℓ (primeSupport N) j,
          ∀ i : Fin ℓ, p i ∈ T := by
        intro p hp i
        have hdvd : ((p i : ℕ) + 1) ∣ (j : ℕ) + 1 := by
          rw [← hprodEq p hp]
          exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
        rw [← hprodEq q₀ hq₀] at hdvd
        have hpp : Prime ((p i : ℕ) + 1) := (hprime p hp i).prime
        obtain ⟨k, _, hk⟩ := (Prime.dvd_finsetProd_iff hpp _).mp hdvd
        have heq : ((p i : ℕ) + 1) = ((q₀ k : ℕ) + 1) :=
          (Nat.prime_dvd_prime_iff_eq (hprime p hp i) (hprime q₀ hq₀ k)).mp hk
        have hfin : p i = q₀ k := Fin.ext (by omega)
        rw [hT, hfin]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
      have hsubset : powFibreOn N ℓ (primeSupport N) j
          ⊆ Fintype.piFinset (fun _ : Fin ℓ => T) := by
        intro p hp
        rw [Fintype.mem_piFinset]
        exact hmaps p hp
      refine le_trans (Finset.card_le_card hsubset) ?_
      rw [Fintype.card_piFinset]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact Nat.pow_le_pow_left hTcard ℓ
  exact_mod_cast le_trans hnat (le_refl _)

/-- **The `ℓ²` mass of the `ℓ`-th power of a prime-supported vector.** -/
theorem primePowerSupportSum_normSq_convPow_le_of_prime_support (N ℓ : ℕ) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1)) :
    ∑ j : Fin (N ^ ℓ), ‖convPow N ℓ a j‖ ^ 2
      ≤ (ℓ : ℝ) ^ ℓ * (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ :=
  sum_normSq_convPow_le_of_support N ℓ a (primeSupport N)
    (fun n hn => by
      rw [primeSupport, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hsupp n hn⟩)
    (fun j => powFibreOn_primeSupport_card_le N ℓ j) (by positivity)

/-- The level sets of `F` and of `F^ℓ` coincide at the powered threshold. -/
theorem largeValues_pow_setOf (N ℓ : ℕ) (hℓ : ℓ ≠ 0) (a : Fin N → ℂ) (S : Set ℝ)
    {V : ℝ} (hV : 0 ≤ V) :
    {t ∈ S | V ^ ℓ ≤ ‖dirPoly (N ^ ℓ) (convPow N ℓ a) t‖}
      = {t ∈ S | V ≤ ‖dirPoly N a t‖} := by
  ext t
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  intro _
  rw [dirPoly_convPow, norm_pow]
  constructor
  · intro h
    exact le_of_pow_le_pow_left₀ hℓ (norm_nonneg _) h
  · intro h
    exact pow_le_pow_left₀ hV h ℓ

/-- **The adapted-moment level-set bound for a prime-supported polynomial.**  Choosing `ℓ` so
that `N^ℓ` matches the range length makes this the well-spaced large-value count for short prime
polynomials. -/
private theorem volume_largeValues_pow_symm_le_of_prime_support (N ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ (2 * ℓ) * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N a t‖}
      ≤ 2 * ((T + 4 * ((N ^ ℓ : ℕ) : ℝ) * (1 + Real.log ((N ^ ℓ : ℕ) : ℝ)))
          * ((ℓ : ℝ) ^ ℓ * (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ)) := by
  have hVl : (0 : ℝ) ≤ V ^ ℓ := by positivity
  have hbase := volume_largeValues_symm_le (N ^ ℓ) (convPow N ℓ a) hT hVl
  rw [largeValues_pow_setOf N ℓ hℓ a (Set.Icc (-T) T) hV] at hbase
  have hpow : (V ^ ℓ) ^ 2 = V ^ (2 * ℓ) := by
    rw [← pow_mul, mul_comm]
  rw [hpow] at hbase
  refine le_trans hbase ?_
  have hlogNl : (0 : ℝ) ≤ Real.log ((N ^ ℓ : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N ^ ℓ) with h | h
    · simp [h]
    · have h1 : 1 ≤ N ^ ℓ := h
      exact Real.log_nonneg (by exact_mod_cast h1)
  have hcast : (0 : ℝ) ≤ ((N ^ ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfactor : (0 : ℝ)
      ≤ T + 4 * ((N ^ ℓ : ℕ) : ℝ) * (1 + Real.log ((N ^ ℓ : ℕ) : ℝ)) := by nlinarith
  have hstep := mul_le_mul_of_nonneg_left
    (primePowerSupportSum_normSq_convPow_le_of_prime_support N ℓ a hsupp) hfactor
  linarith

end RHTower.Sieve
